import AAG11InnerLiftEnergy

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.AnnularSourceGraph

theorem complexSmoothRadialCore_ext {dimension : ℕ} {first second : complexSmoothRadialCore dimension}
    (same : ∀ radius, first.val.1 radius = second.val.1 radius) : first = second := by
  have accepted : complexCoreToAccepted dimension first = complexCoreToAccepted dimension second :=
    smoothRadialCore_ext same
  exact congrArg (acceptedCoreToComplex dimension) accepted

def smoothScalarRadialCore (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile) :
    ComplexEuclidean 1 →ₗ[ℂ] complexSmoothRadialCore 1 where
  toFun vector := acceptedCoreToComplex 1 (smoothRadialFunctionCore (fun radius => profile radius • vector)
    (smooth.smul contDiff_const))
  map_add' first second := by
    apply complexSmoothRadialCore_ext
    intro radius
    exact smul_add (profile radius) first second
  map_smul' scalar vector := by
    apply complexSmoothRadialCore_ext
    intro radius
    exact smul_comm (profile radius) scalar vector

theorem smoothScalarRadialCore_value (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) (radius : ℝ) :
    (smoothScalarRadialCore profile smooth vector).val.1 radius = profile radius • vector := rfl

theorem smoothScalarRadialCore_slope (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) (radius : ℝ) :
    (smoothScalarRadialCore profile smooth vector).val.2 radius = deriv profile radius • vector :=
  (((smooth.differentiable (by simp) radius).hasDerivAt).smul_const vector).deriv

def annularInnerLiftMode (lower : ℝ) (mode : HighAnnularMode) :
    ComplexEuclidean 1 →ₗ[ℂ] complexSmoothRadialCore 1 :=
  smoothScalarRadialCore (annularInnerLiftProfile lower mode) (annularInnerLiftProfile_smooth lower mode)

theorem annularInnerLiftMode_inner (lower : ℝ) (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
      (annularInnerLiftMode lower mode vector).val.1 lower = vector := by
  rw [show (annularInnerLiftMode lower mode vector).val.1 lower =
    annularInnerLiftProfile lower mode lower • vector from rfl, annularInnerLiftProfile_inner]
  change (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℝ) •
    ((Real.sqrt (annularFrequency mode.val.1 mode.val.2))⁻¹ • vector) = vector
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (annularFrequency_one_le _ _))).ne', one_smul]

theorem annularInnerLiftMode_outer (lower : ℝ) (bounded : lower < 1)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    (annularInnerLiftMode lower mode vector).val.1 1 = 0 := by
  change annularInnerLiftProfile lower mode 1 • vector = 0
  rw [annularInnerLiftProfile_outer lower bounded, zero_smul]

theorem annularInnerLiftMode_energy_sq (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (annularInnerLiftMode lower mode vector)‖ ^ 2 ≤
      annularInnerLiftSquaredConstant lower length * ‖vector‖ ^ 2 := by
  have literal := annularModeEnergyCore_norm_sq lower length positive bounded.le mode.val.1 mode.val.2
    (annularInnerLiftMode lower mode vector)
  rw [annularInnerLiftMode_outer lower bounded, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at literal
  have factorization : (∫ radius in lower..1,
      radius * (‖(annularInnerLiftMode lower mode vector).val.2 radius‖ ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 * ‖(annularInnerLiftMode lower mode vector).val.1 radius‖ ^ 2)) =
      (∫ radius in lower..1, radius * (deriv (annularInnerLiftProfile lower mode) radius ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 * annularInnerLiftProfile lower mode radius ^ 2)) * ‖vector‖ ^ 2 := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro radius _
    change radius * (‖(smoothScalarRadialCore _ _ vector).val.2 radius‖ ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 *
        ‖annularInnerLiftProfile lower mode radius • vector‖ ^ 2) = _
    rw [smoothScalarRadialCore_slope, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [literal, factorization]
  exact mul_le_mul_of_nonneg_right (annularInnerLiftProfile_energy_integral lower length positive bounded mode) (sq_nonneg _)

def annularInnerLiftConstant (lower length : ℝ) : ℝ := Real.sqrt (annularInnerLiftSquaredConstant lower length)

theorem annularInnerLiftMode_energy_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (annularInnerLiftMode lower mode vector)‖ ≤ annularInnerLiftConstant lower length * ‖vector‖ := by
  unfold annularInnerLiftConstant
  have rooted := Real.sqrt_le_sqrt (annularInnerLiftMode_energy_sq lower length positive bounded mode vector)
  simpa only [Real.sqrt_mul (annularInnerLiftSquaredConstant_nonnegative lower length),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using rooted

end Grad.AnnularVariational
