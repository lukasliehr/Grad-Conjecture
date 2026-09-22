import AOD4IntegratedRadialRecurrence

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.CircularHighRegularity

/-- Mixed energy at fixed total order grade+2. -/
def mixedRadialEnergy (grade radial : ℕ) (energy : ℕ → ℤ → ℝ) (mode : ℤ) : ℝ :=
  |(mode : ℝ)| ^ (2 * (grade + 2 - radial)) * energy radial mode

private theorem weighted_recurrence_scalar (grade order : ℕ) (paid : order ≤ grade)
    (frequency constant ceiling : ℝ) (high : 1 ≤ frequency) (constantNonnegative : 0 ≤ constant)
    (energy : ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ energy index) (forcing : ℝ)
    (recurrence : energy (order + 2) ≤ 4 *
      (constant * (∑ index ∈ Finset.range (order + 1), energy (order - index + 1)) +
        frequency ^ 4 * constant * (∑ index ∈ Finset.range (order + 1), energy (order - index)) +
        ceiling ^ 4 * energy order + forcing)) :
    frequency ^ (2 * (grade + 2 - (order + 2))) * energy (order + 2) ≤ 4 *
      (constant * (∑ index ∈ Finset.range (order + 1),
        frequency ^ (2 * (grade + 2 - (order - index + 1))) * energy (order - index + 1)) +
      constant * (∑ index ∈ Finset.range (order + 1),
        frequency ^ (2 * (grade + 2 - (order - index))) * energy (order - index)) +
      ceiling ^ 4 * (frequency ^ (2 * (grade + 2 - order)) * energy order) +
      frequency ^ (2 * (grade - order)) * forcing) := by
  let weight := frequency ^ (2 * (grade - order))
  have firstBound : weight * (∑ index ∈ Finset.range (order + 1), energy (order - index + 1)) ≤
      ∑ index ∈ Finset.range (order + 1),
        frequency ^ (2 * (grade + 2 - (order - index + 1))) * energy (order - index + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index member
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ high (by omega)) (nonnegative _)
  have secondBound : weight * frequency ^ 4 * (∑ index ∈ Finset.range (order + 1), energy (order - index)) ≤
      ∑ index ∈ Finset.range (order + 1),
        frequency ^ (2 * (grade + 2 - (order - index))) * energy (order - index) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index member
    have factor : weight * frequency ^ 4 ≤ frequency ^ (2 * (grade + 2 - (order - index))) := by
      dsimp only [weight]
      rw [← pow_add]
      exact pow_le_pow_right₀ high (by omega)
    exact mul_le_mul_of_nonneg_right factor (nonnegative _)
  have thirdBound : weight * energy order ≤ frequency ^ (2 * (grade + 2 - order)) * energy order :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ high (by omega)) (nonnegative _)
  have scaled : weight * energy (order + 2) ≤ 4 *
      (constant * (weight * ∑ index ∈ Finset.range (order + 1), energy (order - index + 1)) +
        constant * (weight * frequency ^ 4 * ∑ index ∈ Finset.range (order + 1), energy (order - index)) +
        ceiling ^ 4 * (weight * energy order) + weight * forcing) :=
    (mul_le_mul_of_nonneg_left recurrence (pow_nonneg (zero_le_one.trans high) _)).trans_eq (by ring)
  have bound := scaled.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left firstBound constantNonnegative)
      (mul_le_mul_of_nonneg_left secondBound constantNonnegative))
      (mul_le_mul_of_nonneg_left thirdBound (by positivity : 0 ≤ ceiling ^ 4))) le_rfl)
    (by norm_num : (0 : ℝ) ≤ 4))
  simpa only [show grade + 2 - (order + 2) = grade - order by omega] using bound

/-- Angular weights absorb every lower total order in the differentiated ODE. -/
theorem mixedRadialEnergy_recurrence (grade order : ℕ) (paid : order ≤ grade)
    (constant ceiling : ℝ) (constantNonnegative : 0 ≤ constant)
    (energy : ℕ → ℤ → ℝ) (nonnegative : ∀ radial mode, 0 ≤ energy radial mode)
    (forcing : ℤ → ℝ) (mode : ℤ) (high : mode ∉ Grad.Constraints.lowAngularModes)
    (recurrence : energy (order + 2) mode ≤ 4 *
      (constant * (∑ index ∈ Finset.range (order + 1), energy (order - index + 1) mode) +
        (mode : ℝ) ^ 4 * constant * (∑ index ∈ Finset.range (order + 1), energy (order - index) mode) +
        ceiling ^ 4 * energy order mode + forcing mode)) :
    mixedRadialEnergy grade (order + 2) energy mode ≤ 4 *
      (constant * (∑ index ∈ Finset.range (order + 1), mixedRadialEnergy grade (order - index + 1) energy mode) +
        constant * (∑ index ∈ Finset.range (order + 1), mixedRadialEnergy grade (order - index) energy mode) +
        ceiling ^ 4 * mixedRadialEnergy grade order energy mode +
        |(mode : ℝ)| ^ (2 * (grade - order)) * forcing mode) := by
  have one : (1 : ℝ) ≤ |(mode : ℝ)| := by
    have square := Grad.CircularHighWeak.highMode_sq mode high
    nlinarith [abs_nonneg (mode : ℝ)]
  have even : |(mode : ℝ)| ^ 4 = (mode : ℝ) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, sq_abs, ← pow_mul]
  apply weighted_recurrence_scalar grade order paid |(mode : ℝ)| constant ceiling one constantNonnegative
    (fun radial => energy radial mode) (fun radial => nonnegative radial mode) (forcing mode)
  simpa only [even] using recurrence

end Grad.CircularHighRegularity
