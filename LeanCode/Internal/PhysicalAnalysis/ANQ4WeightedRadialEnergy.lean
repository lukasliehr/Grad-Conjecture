import ANQ3RadialAngularCompatibility

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.AnnularSourceGraph

private theorem angularScalar_norm_sq (mode : ℤ) (order : ℕ) :
    ‖(Complex.I * (mode : ℂ)) ^ order‖ ^ 2 = |(mode : ℝ)| ^ (2 * order) := by
  have integer : ‖(mode : ℂ)‖ = |(mode : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul, integer, ← pow_mul]
  rw [Nat.mul_comm order 2]

/-- The genuine completed angular mode relation transfers to BOTH
radial H1 coordinates; consequently the full radial energy has weight |m|^(2a). -/
theorem diskRadial_power_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) (mode : ℤ) :
    ‖diskRadial lower positive bounded mode derivative.val‖ ^ 2 =
      |(mode : ℝ)| ^ (2 * order) * ‖diskRadial lower positive bounded mode field.val‖ ^ 2 := by
  have first := congrArg (fun radial : WeightedRadialH1 1 lower => ‖radial‖ ^ 2)
    (diskRadial_highAngular_self lower positive bounded mode derivative).symm
  have second := congrArg (fun current : highDiskGrade =>
    ‖diskRadial lower positive bounded mode current.val‖ ^ 2) (modeLaw mode)
  have third := diskRadial_norm_sq_smul lower positive bounded mode ((Complex.I * (mode : ℂ)) ^ order)
    (highDiskMode mode field).val
  have fourth := congrArg₂ (fun scalar energy : ℝ => scalar * energy)
    (angularScalar_norm_sq mode order)
    (congrArg (fun radial : WeightedRadialH1 1 lower => ‖radial‖ ^ 2)
      (diskRadial_highAngular_self lower positive bounded mode field))
  exact first.trans (second.trans (third.trans fourth))

theorem diskRadial_weighted_finite_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) * ‖diskRadial lower positive bounded mode field.val‖ ^ 2) ≤
      diskRadialBound ^ 2 * ‖derivative‖ ^ 2 := by
  have equality := Finset.sum_congr (s₁ := modes) rfl (fun mode _ =>
    (diskRadial_power_energy lower positive bounded order field derivative modeLaw mode).symm)
  exact equality.trans_le (diskRadial_finite_energy lower positive bounded derivative.val modes)

theorem diskRadial_weighted_summable_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) :
    Summable (fun mode : ℤ => |(mode : ℝ)| ^ (2 * order) * ‖diskRadial lower positive bounded mode field.val‖ ^ 2) :=
  summable_of_sum_le (fun _ => mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
    (diskRadial_weighted_finite_energy lower positive bounded order field derivative modeLaw)

theorem diskRadial_weighted_total_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) :
    (∑' mode : ℤ, |(mode : ℝ)| ^ (2 * order) * ‖diskRadial lower positive bounded mode field.val‖ ^ 2) ≤
      diskRadialBound ^ 2 * ‖derivative‖ ^ 2 :=
  (diskRadial_weighted_summable_energy lower positive bounded order field derivative modeLaw).tsum_le_of_sum_le
    (diskRadial_weighted_finite_energy lower positive bounded order field derivative modeLaw)

end Grad.CircularHighRegularity
