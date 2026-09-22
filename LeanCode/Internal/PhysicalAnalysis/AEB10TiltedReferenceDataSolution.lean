import AEB9TiltedReferenceFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational

local instance tiltedDataZero_normedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) := inferInstance

local instance tiltedDataZero_seminormedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    SeminormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) :=
  (tiltedDataZero_normedGroup lower length positive collar lengthPositive).toSeminormedAddCommGroup

local instance tiltedDataZero_realNormedSpace (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedSpace ℝ (annularInnerZero lower length positive collar lengthPositive) :=
  (annularInnerZero_realInner lower length positive collar lengthPositive).toNormedSpace

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularTiltVariationalRHS (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularInnerZero lower length positive bounded lengthPositive →L[ℝ] ℝ :=
  (annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source -
    annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularInnerLift lower length positive bounded innerValue)).comp
        (annularZeroRealInclusion lower length positive bounded lengthPositive)

def annularTiltZeroSolution (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularInnerZero lower length positive bounded lengthPositive :=
  annularTiltDualInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
    (annularTiltVariationalRHS parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)


theorem annularTiltZeroSolution_real (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularTiltZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength
      (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test =
      annularTiltVariationalRHS parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue test :=
  annularTiltDualInverse_solves parameters lower length positive bounded lengthPositive widthHalf widthLength _ test

/-- The tilted reference solution with independently prescribed normalized bulk, outer, and inner data. -/
def annularTiltVariationalSolution (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularEnergySpace lower length positive :=
  annularInnerLift lower length positive bounded innerValue +
    annularZeroInclusion lower length positive bounded lengthPositive
      (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)

theorem annularTiltVariationalSolution_real (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test.val =
      annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  have law := annularTiltZeroSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue test
  change annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).val test.val =
    annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val -
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
        (annularInnerLift lower length positive bounded innerValue) test.val at law
  unfold annularTiltVariationalSolution
  rw [map_add, add_apply]
  change _ + annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength
    (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).val test.val = _
  linarith only [law]

theorem annularTiltVariationalSolution_weak (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test.val =
      annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  let solution := annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have realLaw (point : annularInnerZero lower length positive bounded lengthPositive) :
      (annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength solution point.val).re =
        (annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val).re :=
    (annularTiltForm_literal parameters lower length positive lengthPositive widthHalf widthLength solution point.val).symm.trans
      ((annularTiltVariationalSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue point).trans
        (annularTiltFunctional_literal parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val))
  apply Complex.ext (realLaw test)
  have imaginaryLaw := realLaw (Complex.I • test)
  have formLaw := congrArg Complex.re
    (annularTiltFormValue_test_smul parameters lower length positive lengthPositive widthHalf widthLength solution test.val Complex.I)
  have forcingLaw := congrArg Complex.re
    (annularTiltFunctionalValue_test_smul parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val Complex.I)
  have equality := formLaw.symm.trans (imaginaryLaw.trans forcingLaw)
  simpa using equality

theorem annularTiltVariationalSolution_inner (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularEnergyTrace lower length positive bounded lengthPositive 0
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) = innerValue := by
  unfold annularTiltVariationalSolution
  rw [map_add, annularInnerLift_inner]
  have zero := (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).property
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (annularZeroInclusion lower length positive bounded lengthPositive
      (annularTiltZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)) = 0 at zero
  rw [zero, add_zero]

end Inverse
end Grad.AnnularTiltedReference
