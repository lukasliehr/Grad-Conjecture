import SM12AxisCore

noncomputable section

open scoped Topology ComplexConjugate

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState

theorem cellFrequency_sublevel_finite (bound : ℝ) :
    Set.Finite {cell : ℤ | cellFrequency cell ≤ bound} := by
  let upper := max bound 1
  have upperPositive : 0 < upper := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have thresholdPositive : 0 < (upper ^ 2)⁻¹ := inv_pos.mpr (pow_pos upperPositive 2)
  have small : ∀ᶠ cell in Filter.cofinite, (cellFrequency cell)⁻¹ ^ 2 < (upper ^ 2)⁻¹ :=
    inverseCellFrequency_sq_summable.tendsto_cofinite_zero.eventually (gt_mem_nhds thresholdPositive)
  apply (Filter.eventually_cofinite.mp small).subset
  intro cell below
  apply not_lt_of_ge
  rw [inv_pow]
  exact (inv_le_inv₀ (pow_pos upperPositive 2) (pow_pos (cellFrequency_pos cell) 2)).mpr
    (pow_le_pow_left₀ (cellFrequency_pos cell).le (below.trans (le_max_left _ _)) 2)

def axisSmoothing {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) : AxisCore width Value →ₗ[ℂ] AxisCore width Value :=
  boundedAxisMultiplier width (fun cell => eta (cellFrequency cell / scale)) 1 zero_le_one
    (fun cell => by rw [Real.norm_eq_abs, abs_of_nonneg (eta_range _).1]; exact (eta_range _).2)

theorem axisSmoothing_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (values : AxisCore width Value) (cell : ℤ) :
    (axisSmoothing width scale values).1 cell = (eta (cellFrequency cell / scale) : ℂ) • values.1 cell := rfl

def axisScaleDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (order : ℕ) (scale : ℝ) : AxisCore width Value →ₗ[ℂ] AxisCore width Value :=
  boundedAxisMultiplier width (fun cell => scaleMultiplier order (cellFrequency cell) scale)
    (‖scale ^ (-(order : ℝ))‖ * profileBound order)
    (mul_nonneg (norm_nonneg _) (profileBound_nonnegative order)) (by
      intro cell
      rw [scaleMultiplier, norm_mul]
      exact mul_le_mul_of_nonneg_left (scaleProfile_norm_le order _) (norm_nonneg _))

theorem axisScaleDerivative_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (order : ℕ) (scale : ℝ) (values : AxisCore width Value) (cell : ℤ) :
    (axisScaleDerivative width order scale values).1 cell =
      (scaleMultiplier order (cellFrequency cell) scale : ℂ) • values.1 cell := rfl

theorem axisScaleDerivative_zero {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) : axisScaleDerivative (Value := Value) width 0 scale = axisSmoothing width scale := by
  ext values cell
  change (scaleMultiplier 0 (cellFrequency cell) scale : ℂ) • values.1 cell = _
  rw [scaleMultiplier_zero]
  rfl

theorem axisSmoothing_finite_support {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (positive : 0 < scale) (values : AxisCore width Value) :
    Set.Finite (Function.support (axisSmoothing width scale values).1) := by
  apply (cellFrequency_sublevel_finite (2 * scale)).subset
  intro cell nonzero
  by_contra outside
  have cutoffZero : eta (cellFrequency cell / scale) = 0 :=
    eta_zero _ ((le_div_iff₀ positive).mpr (le_of_lt (lt_of_not_ge outside)))
  apply nonzero
  rw [axisSmoothing_apply, cutoffZero, Complex.ofReal_zero, zero_smul]

theorem axisSmoothing_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (positive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (values : AxisCore width Value) :
    ‖axisToGrade width upper (axisSmoothing width scale values)‖ ≤
      (2 * scale) ^ (upper - lower) * ‖axisToGrade width lower values‖ := by
  apply axis_norm_le_of_weighted_bound _ _ _ _ _ _ (by positivity)
  intro cell
  rw [axisSmoothing_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (eta_range _).1, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right
    (smoothing_weight_bound (cellFrequency cell) scale (cellFrequency_pos cell) positive lower upper ordered)
    (norm_nonneg (values.1 cell))).trans_eq (by ring)

theorem axisRemainder_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (values : AxisCore width Value) (cell : ℤ) :
    (values - axisSmoothing width scale values).1 cell =
      ((1 - eta (cellFrequency cell / scale) : ℝ) : ℂ) • values.1 cell := by
  change values.1 cell - (eta (cellFrequency cell / scale) : ℂ) • values.1 cell = _
  rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]

theorem axisRemainder_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (positive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (values : AxisCore width Value) :
    ‖axisToGrade width lower (values - axisSmoothing width scale values)‖ ≤
      scale ^ ((lower : ℝ) - (upper : ℝ)) * ‖axisToGrade width upper values‖ := by
  rw [rpow_grade_difference scale positive.le lower upper ordered]
  apply axis_norm_le_of_weighted_bound _ _ _ _ _ _ (by positivity)
  intro cell
  rw [axisRemainder_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (eta_range _).2), ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right
    (remainder_weight_bound (cellFrequency cell) scale (cellFrequency_pos cell) positive lower upper ordered)
    (norm_nonneg (values.1 cell))).trans_eq (by ring)

theorem axisScaleDerivative_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (positive : 0 < scale) (lower upper order : ℕ) (positiveOrder : 0 < order)
    (values : AxisCore width Value) :
    ‖axisToGrade width upper (axisScaleDerivative width order scale values)‖ ≤
      ((2 : ℝ) ^ upper * profileBound order) * scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) *
        ‖axisToGrade width lower values‖ := by
  apply axis_norm_le_of_weighted_bound _ _ _ _ _ _
    (mul_nonneg (mul_nonneg (by positivity) (profileBound_nonnegative order))
      (Real.rpow_nonneg positive.le _))
  intro cell
  rw [axisScaleDerivative_apply, norm_smul, Complex.norm_real, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right
    (derivative_weight_bound (cellFrequency cell) scale (cellFrequency_pos cell) positive lower upper order positiveOrder)
    (norm_nonneg (values.1 cell))).trans_eq (by ring)

/-- In particular the prescribed axis shift is literally `q+1`, with no loss. -/
theorem shifted_axisSmoothing_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width scale : ℝ) (positive : 0 < scale) (lower upper shift : ℕ) (ordered : lower ≤ upper)
    (values : AxisCore width Value) :
    ‖axisToGrade width (upper + shift) (axisSmoothing width scale values)‖ ≤
      (2 * scale) ^ (upper - lower) * ‖axisToGrade width (lower + shift) values‖ := by
  simpa only [Nat.add_sub_add_right] using
    axisSmoothing_norm_le width scale positive (lower + shift) (upper + shift) (Nat.add_le_add_right ordered shift) values

def AxisReality {dimension : ℕ} {width : ℝ} (values : AxisCore width (ComplexEuclidean dimension)) : Prop :=
  ∀ cell coordinate, conj (values.1 (-cell) coordinate) = values.1 cell coordinate

theorem axisScaleDerivative_reality {dimension : ℕ} (width : ℝ) (order : ℕ) (scale : ℝ)
    (values : AxisCore width (ComplexEuclidean dimension)) (real : AxisReality values) :
    AxisReality (axisScaleDerivative width order scale values) := by
  intro cell coordinate
  simp only [axisScaleDerivative_apply, PiLp.smul_apply, smul_eq_mul, map_mul,
    cellFrequency_neg, Complex.conj_ofReal]
  exact congrArg (fun value : ℂ => (scaleMultiplier order (cellFrequency cell) scale : ℂ) * value)
    (real cell coordinate)

end Grad.SmoothingFamily
