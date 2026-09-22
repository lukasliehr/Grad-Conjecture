import AEB10TiltedReferenceDataSolution

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularTiltedReference

open Grad.CartesianState Grad.AnnularVariational

local instance tiltedBoundZero_normedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) := inferInstance

local instance tiltedBoundZero_seminormedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    SeminormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) :=
  (tiltedBoundZero_normedGroup lower length positive collar lengthPositive).toSeminormedAddCommGroup

local instance tiltedBoundZero_realNormedSpace (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedSpace ℝ (annularInnerZero lower length positive collar lengthPositive) :=
  (annularInnerZero_realInner lower length positive collar lengthPositive).toNormedSpace

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularTiltVariationalSolution_unique (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (candidate : annularEnergySpace lower length positive)
    (innerLaw : annularEnergyTrace lower length positive bounded lengthPositive 0 candidate = innerValue)
    (weakLaw : ∀ test : annularInnerZero lower length positive bounded lengthPositive,
      annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength candidate test.val =
        annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val) :
    candidate = annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue := by
  let solution := annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have innerSolution := annularTiltVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let difference : annularInnerZero lower length positive bounded lengthPositive :=
    ⟨candidate - solution, by
      change annularEnergyTrace lower length positive bounded lengthPositive 0 (candidate - solution) = 0
      rw [map_sub, innerLaw, innerSolution, sub_self]⟩
  have first := congrArg Complex.re (weakLaw difference)
  have second := annularTiltVariationalSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue difference
  rw [← annularTiltForm_literal, ← annularTiltFunctional_literal] at first
  have zero : annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
      (candidate - solution) (candidate - solution) = 0 := by
    have expanded : annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
        (candidate - solution) (candidate - solution) =
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength candidate difference.val -
        annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength solution difference.val :=
      congrArg (fun functional : annularEnergySpace lower length positive →L[ℝ] ℝ => functional difference.val)
        ((annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength).map_sub candidate solution)
    linarith only [expanded, first, second]
  have coercive := annularTiltForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength (candidate - solution)
  rw [zero] at coercive
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (candidate - solution)]

theorem annularTiltZeroSolution_bound (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue‖ ≤
      (16 : ℝ) * (annularForcingSize lower length source +
        4 * annularInnerLiftConstant lower length * ‖innerValue‖) := by
  let zeroSolution := annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let lift := annularInnerLift lower length positive bounded innerValue
  have law := annularTiltZeroSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue zeroSolution
  have coercive := annularTiltZeroForm_coercive_bound parameters lower length positive bounded lengthPositive widthHalf widthLength zeroSolution
  have functional := annularTiltFunctionalValue_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val
  have realFunctional : annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val ≤
      annularForcingSize lower length source * ‖zeroSolution‖ := by
    rw [annularTiltFunctional_literal]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans functional)
  have formBound := annularTiltForm_abs_bound parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val
  have zeroNormValue : ‖zeroSolution.val‖ = ‖zeroSolution‖ := rfl
  rw [zeroNormValue] at formBound
  have liftBound := annularInnerLift_bound lower length positive bounded innerValue
  have productBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left liftBound (by norm_num : (0 : ℝ) ≤ 4)) (norm_nonneg zeroSolution)
  change annularTiltZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength zeroSolution zeroSolution =
    annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val -
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val at law
  have negative : -annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val ≤
      4 * annularInnerLiftConstant lower length * ‖innerValue‖ * ‖zeroSolution‖ :=
    (neg_le_abs _).trans (formBound.trans (by simpa only [lift, mul_assoc] using productBound))
  have quadratic : (1 / 16 : ℝ) * ‖zeroSolution‖ ^ 2 ≤
      (annularForcingSize lower length source + 4 * annularInnerLiftConstant lower length * ‖innerValue‖) * ‖zeroSolution‖ := by
    nlinarith only [coercive, law, realFunctional, negative]
  have sizeNonnegative : 0 ≤ annularForcingSize lower length source := by
    unfold annularForcingSize annularTraceConstant
    positivity
  have liftNonnegative : 0 ≤ annularInnerLiftConstant lower length := Real.sqrt_nonneg _
  by_cases zeroNorm : ‖zeroSolution‖ = 0
  · change ‖zeroSolution‖ ≤ _
    rw [zeroNorm]
    positivity
  · have normPositive := lt_of_le_of_ne (norm_nonneg zeroSolution) (Ne.symm zeroNorm)
    change ‖zeroSolution‖ ≤ _
    nlinarith only [quadratic, normPositive]

/-- Fixed-collar tilted reference bound in the exact normalized energy norm at the original width. Uniform outer trace and incoming lift bounds are separate prerequisites. -/
theorem annularTiltVariationalSolution_bound (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue‖ ≤
      annularInnerLiftConstant lower length * ‖innerValue‖ +
        (16 : ℝ) * (annularForcingSize lower length source +
          4 * annularInnerLiftConstant lower length * ‖innerValue‖) := by
  have zeroBound := annularTiltZeroSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have liftBound := annularInnerLift_bound lower length positive bounded innerValue
  exact (norm_add_le _ _).trans (add_le_add liftBound zeroBound)

end Inverse

end Grad.AnnularTiltedReference
