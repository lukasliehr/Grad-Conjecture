import AEF8UniformTiltFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularUniformBoundary

open Grad.CartesianState Grad.AnnularVariational
open Grad.AnnularTiltedReference

local instance uniformZero_normedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) := inferInstance

local instance uniformZero_seminormedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    SeminormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) :=
  (uniformZero_normedGroup lower length positive collar lengthPositive).toSeminormedAddCommGroup

local instance uniformZero_realNormedSpace (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedSpace ℝ (annularInnerZero lower length positive collar lengthPositive) :=
  (annularInnerZero_realInner lower length positive collar lengthPositive).toNormedSpace

section Bound

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The exact constructed tilted solution obeys a bound independent of the
inner radius.  The proof subtracts the new uniform lift from the already
accepted solution and applies coercivity on the complete zero-trace space. -/
theorem annularTiltVariationalSolution_uniform_bound
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularTiltVariationalSolution parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength source innerValue‖ ≤
      uniformInnerLiftConstant length * ‖innerValue‖ +
        16 * (uniformAnnularForcingSize lower length source +
          4 * uniformInnerLiftConstant length * ‖innerValue‖) := by
  let collar : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let solution := annularTiltVariationalSolution parameters lower length positive collar
    lengthPositive widthHalf widthLength source innerValue
  let lift := uniformInnerLift lower length positive lowerHalf lengthPositive innerValue
  let difference : annularInnerZero lower length positive collar lengthPositive :=
    ⟨solution - lift, by
      change annularEnergyTrace lower length positive collar lengthPositive 0
        (solution - lift) = 0
      rw [map_sub]
      change annularEnergyTrace lower length positive collar lengthPositive 0 solution -
        annularEnergyTrace lower length positive collar lengthPositive 0 lift = 0
      rw [show collar = lowerHalf.trans_lt (by norm_num) from Subsingleton.elim _ _,
        annularTiltVariationalSolution_inner, uniformInnerLift_inner, sub_self]⟩
  have solutionLaw := annularTiltVariationalSolution_real parameters lower length positive
    collar lengthPositive widthHalf widthLength source innerValue difference
  have expanded :
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
        difference.val difference.val =
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
          solution difference.val -
        annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
          lift difference.val := by
    have mapped := congrArg
      (fun functional : annularEnergySpace lower length positive →L[ℝ] ℝ =>
        functional difference.val)
      ((annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength).map_sub
        solution lift)
    simpa only [difference, sub_apply] using mapped
  have law :
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
        difference.val difference.val =
      annularTiltFunctional parameters lower length positive collar lengthPositive
          widthHalf widthLength source difference.val -
        annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
          lift difference.val := expanded.trans (congrArg
    (fun value : ℝ => value - annularTiltForm parameters lower length positive
      lengthPositive widthHalf widthLength lift difference.val) solutionLaw)
  have coercive := annularTiltForm_coercive_bound parameters lower length positive
    lengthPositive widthHalf widthLength difference.val
  have functionalComplex := annularTiltFunctionalValue_uniform_bound parameters lower length
    positive lowerHalf lengthPositive widthHalf widthLength source difference.val
  have realFunctional :
      annularTiltFunctional parameters lower length positive collar lengthPositive
        widthHalf widthLength source difference.val ≤
      uniformAnnularForcingSize lower length source * ‖difference‖ := by
    rw [annularTiltFunctional_literal]
    have estimate := (le_abs_self
      (annularTiltFunctionalValue parameters lower length positive collar lengthPositive
        widthHalf widthLength source difference.val).re).trans
      ((Complex.abs_re_le_norm _).trans functionalComplex)
    simpa only [show ‖difference.val‖ = ‖difference‖ from rfl] using estimate
  have formBound := annularTiltForm_abs_bound parameters lower length positive
    lengthPositive widthHalf widthLength lift difference.val
  have liftBound := uniformInnerLift_bound lower length positive lowerHalf lengthPositive innerValue
  have productBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left liftBound (by norm_num : (0 : ℝ) ≤ 4))
    (norm_nonneg difference)
  have negative :
      -annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
        lift difference.val ≤
      4 * uniformInnerLiftConstant length * ‖innerValue‖ * ‖difference‖ := by
    exact (neg_le_abs _).trans (formBound.trans (by
      simpa only [show ‖difference.val‖ = ‖difference‖ from rfl, lift, mul_assoc]
        using productBound))
  have quadratic : (1 / 16 : ℝ) * ‖difference‖ ^ 2 ≤
      (uniformAnnularForcingSize lower length source +
        4 * uniformInnerLiftConstant length * ‖innerValue‖) * ‖difference‖ := by
    have coercive' : (1 / 16 : ℝ) * ‖difference‖ ^ 2 ≤
        annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
          difference.val difference.val := by
      simpa only [show ‖difference.val‖ = ‖difference‖ from rfl] using coercive
    nlinarith only [coercive', law, realFunctional, negative]
  have differenceBound : ‖difference‖ ≤
      16 * (uniformAnnularForcingSize lower length source +
        4 * uniformInnerLiftConstant length * ‖innerValue‖) := by
    by_cases zeroNorm : ‖difference‖ = 0
    · rw [zeroNorm]
      have sizeNonnegative := uniformAnnularForcingSize_nonnegative lower length source
      have liftConstantNonnegative : 0 ≤ uniformInnerLiftConstant length := Real.sqrt_nonneg _
      positivity
    · have normPositive := lt_of_le_of_ne (norm_nonneg difference) (Ne.symm zeroNorm)
      nlinarith only [quadratic, normPositive]
  have decomposition : solution = lift + difference.val := by
    simp only [difference]
    abel
  have triangle := (congrArg norm decomposition).trans_le (norm_add_le lift difference.val)
  change ‖solution‖ ≤ _
  exact triangle.trans (add_le_add liftBound (by
    simpa only [show ‖difference.val‖ = ‖difference‖ from rfl] using differenceBound))

end Bound

end Grad.AnnularUniformBoundary
