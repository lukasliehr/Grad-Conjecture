import AAG17ActualVariationalInverse

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularVariational

open Grad.CartesianState

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularVariationalSolution_unique (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (candidate : annularEnergySpace lower length positive)
    (innerLaw : annularEnergyTrace lower length positive bounded lengthPositive 0 candidate = innerValue)
    (weakLaw : ∀ test : annularInnerZero lower length positive bounded lengthPositive,
      annularFormValue parameters lower length positive lengthPositive widthHalf widthLength candidate test.val =
        annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val) :
    candidate = annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue := by
  let solution := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have innerSolution := annularVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let difference : annularInnerZero lower length positive bounded lengthPositive :=
    ⟨candidate - solution, by
      change annularEnergyTrace lower length positive bounded lengthPositive 0 (candidate - solution) = 0
      rw [map_sub, innerLaw, innerSolution, sub_self]⟩
  have first := congrArg Complex.re (weakLaw difference)
  have second := annularVariationalSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue difference
  rw [← annularForm_literal, ← annularFunctional_literal] at first
  have zero : annularForm parameters lower length positive lengthPositive widthHalf widthLength
      (candidate - solution) (candidate - solution) = 0 := by
    have expanded : annularForm parameters lower length positive lengthPositive widthHalf widthLength
        (candidate - solution) (candidate - solution) =
      annularForm parameters lower length positive lengthPositive widthHalf widthLength candidate difference.val -
        annularForm parameters lower length positive lengthPositive widthHalf widthLength solution difference.val :=
      congrArg (fun functional : annularEnergySpace lower length positive →L[ℝ] ℝ => functional difference.val)
        ((annularForm parameters lower length positive lengthPositive widthHalf widthLength).map_sub candidate solution)
    linarith only [expanded, first, second]
  have coercive := annularForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength (candidate - solution)
  rw [zero] at coercive
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (candidate - solution)]

theorem annularZeroSolution_bound (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue‖ ≤
      (4 / 3 : ℝ) * (annularForcingSize lower length source +
        4 * annularInnerLiftConstant lower length * ‖innerValue‖) := by
  let zeroSolution := annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let lift := annularInnerLift lower length positive bounded innerValue
  have law := annularZeroSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue zeroSolution
  have coercive := annularZeroForm_coercive_bound parameters lower length positive bounded lengthPositive widthHalf widthLength zeroSolution
  have functional := annularFunctionalValue_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val
  have realFunctional : annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val ≤
      annularForcingSize lower length source * ‖zeroSolution‖ := by
    rw [annularFunctional_literal]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans functional)
  have formBound := annularForm_abs_bound parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val
  have zeroNormValue : ‖zeroSolution.val‖ = ‖zeroSolution‖ := rfl
  rw [zeroNormValue] at formBound
  have liftBound := annularInnerLift_bound lower length positive bounded innerValue
  have productBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left liftBound (by norm_num : (0 : ℝ) ≤ 4)) (norm_nonneg zeroSolution)
  change annularZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength zeroSolution zeroSolution =
    annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source zeroSolution.val -
      annularForm parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val at law
  have negative : -annularForm parameters lower length positive lengthPositive widthHalf widthLength lift zeroSolution.val ≤
      4 * annularInnerLiftConstant lower length * ‖innerValue‖ * ‖zeroSolution‖ :=
    (neg_le_abs _).trans (formBound.trans (by simpa only [lift, mul_assoc] using productBound))
  have quadratic : (3 / 4 : ℝ) * ‖zeroSolution‖ ^ 2 ≤
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

/-- AG20 in the exact energy norm, uniformly at the original analytic width. -/
theorem annularVariationalSolution_bound (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue‖ ≤
      annularInnerLiftConstant lower length * ‖innerValue‖ +
        (4 / 3 : ℝ) * (annularForcingSize lower length source +
          4 * annularInnerLiftConstant lower length * ‖innerValue‖) := by
  have zeroBound := annularZeroSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have liftBound := annularInnerLift_bound lower length positive bounded innerValue
  exact (norm_add_le _ _).trans (add_le_add liftBound zeroBound)

end Inverse

end Grad.AnnularVariational
