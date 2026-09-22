import ANH12DiskFourierTransform

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- Literal U1 multiplier, extended by zero on the five excluded modes. -/
def highMultiplier (mode : ℤ) : ℝ :=
  if mode ∈ lowAngularModes then 0 else 1 - 4 / (mode : ℝ) ^ 2

theorem highMultiplier_high (mode : ℤ) (high : mode ∉ lowAngularModes) :
    highMultiplier mode = 1 - 4 / (mode : ℝ) ^ 2 := if_neg high

theorem highMultiplier_bounds (mode : ℤ) (high : mode ∉ lowAngularModes) :
    (5 / 9 : ℝ) ≤ highMultiplier mode ∧ highMultiplier mode ≤ 1 := by
  rw [highMultiplier_high mode high]
  have square : (9 : ℝ) ≤ (mode : ℝ) ^ 2 := by simpa only [sq_abs] using highMode_sq mode high
  have positive : 0 < (mode : ℝ) ^ 2 := by linarith
  have divided : 4 / (mode : ℝ) ^ 2 ≤ (4 / 9 : ℝ) :=
    (div_le_iff₀ positive).2 (by nlinarith)
  constructor
  · linarith
  · linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) positive.le]

theorem highMultiplier_nonnegative (mode : ℤ) : 0 ≤ highMultiplier mode := by
  by_cases low : mode ∈ lowAngularModes
  · simp [highMultiplier, low]
  · exact (by norm_num : (0 : ℝ) ≤ 5 / 9).trans (highMultiplier_bounds mode low).1

theorem highMultiplier_one_le (mode : ℤ) : highMultiplier mode ≤ 1 := by
  by_cases low : mode ∈ lowAngularModes
  · simp [highMultiplier, low]
  · exact (highMultiplier_bounds mode low).2

theorem highMultiplier_coordinate_bound (mode : ℤ) (field : DiskL2 1) :
    ‖(highMultiplier mode : ℂ) • field‖ ≤ ‖field‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (highMultiplier_nonnegative mode)]
  exact (mul_le_mul_of_nonneg_right (highMultiplier_one_le mode) (norm_nonneg _)).trans_eq (one_mul _)

def highDiagonalLinear : DiskFourier →ₗ[ℂ] DiskFourier where
  toFun field := ⟨fun mode => (highMultiplier mode : ℂ) • field mode,
    (lp.memℓp field).mono' (fun mode => highMultiplier_coordinate_bound mode (field mode))⟩
  map_add' first second := lp.ext (funext (fun mode => smul_add _ _ _))
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    change (highMultiplier mode : ℂ) • (scalar • field mode) =
      scalar • ((highMultiplier mode : ℂ) • field mode)
    exact smul_comm _ _ _

def highDiagonal : DiskFourier →L[ℂ] DiskFourier :=
  highDiagonalLinear.mkContinuous 1 (fun field => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (fun mode => highMultiplier_coordinate_bound mode (field mode)))

theorem highDiagonal_apply (field : DiskFourier) (mode : ℤ) :
    highDiagonal field mode = (highMultiplier mode : ℂ) • field mode := rfl

theorem highDiagonal_bound (field : DiskFourier) : ‖highDiagonal field‖ ≤ ‖field‖ :=
  lp.norm_mono (by norm_num) (fun mode => highMultiplier_coordinate_bound mode (field mode))

theorem disk_realScalar_inner (scalar : ℝ) (first second : DiskL2 1) :
    inner ℂ ((scalar : ℂ) • first) second = inner ℂ first ((scalar : ℂ) • second) := by
  rw [inner_smul_left, inner_smul_right]
  simp

theorem disk_realScalar_energy (scalar : ℝ) (field : DiskL2 1) :
    (inner ℂ field ((scalar : ℂ) • field)).re = scalar * ‖field‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change ((scalar : ℂ) * (‖field‖ : ℂ) ^ 2).re = _
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem highDiagonal_symmetric (first second : DiskFourier) :
    inner ℂ (highDiagonal first) second = inner ℂ first (highDiagonal second) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  exact disk_realScalar_inner (highMultiplier mode) (first mode) (second mode)

theorem highDiagonal_energy (field : DiskFourier) :
    (inner ℂ field (highDiagonal field)).re =
      ∑' mode : ℤ, highMultiplier mode * ‖field mode‖ ^ 2 := by
  rw [lp.inner_eq_tsum]
  have realSum := (RCLike.reCLM : ℂ →L[ℝ] ℝ).map_tsum (lp.summable_inner field (highDiagonal field))
  exact realSum.trans (tsum_congr (fun mode => disk_realScalar_energy (highMultiplier mode) (field mode)))

theorem highDiagonal_nonnegative (field : DiskFourier) :
    0 ≤ (inner ℂ field (highDiagonal field)).re := by
  rw [highDiagonal_energy]
  exact tsum_nonneg (fun mode => mul_nonneg (highMultiplier_nonnegative mode) (sq_nonneg _))

theorem highDiagonal_coercive (field : DiskFourier)
    (high : ∀ mode ∈ lowAngularModes, field mode = 0) :
    (5 / 9 : ℝ) * ‖field‖ ^ 2 ≤ (inner ℂ field (highDiagonal field)).re := by
  have summable : Summable (fun mode : ℤ => ‖field mode‖ ^ 2) := by
    have member := lp.memℓp field
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member
    simpa using member
  have weighted : Summable (fun mode : ℤ => highMultiplier mode * ‖field mode‖ ^ 2) :=
    summable.of_nonneg_of_le
      (fun mode => mul_nonneg (highMultiplier_nonnegative mode) (sq_nonneg _))
      (fun mode => (mul_le_mul_of_nonneg_right (highMultiplier_one_le mode) (sq_nonneg _)).trans_eq (one_mul _))
  have termBound (mode : ℤ) : (5 / 9 : ℝ) * ‖field mode‖ ^ 2 ≤ highMultiplier mode * ‖field mode‖ ^ 2 := by
    by_cases low : mode ∈ lowAngularModes
    · rw [high mode low, norm_zero, zero_pow (by decide), mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (highMultiplier_bounds mode low).1 (sq_nonneg _)
  have normLaw := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normLaw
  rw [normLaw, highDiagonal_energy, ← tsum_mul_left]
  exact (summable.mul_left (5 / 9)).tsum_le_tsum termBound weighted

end Grad.CircularHighWeak
