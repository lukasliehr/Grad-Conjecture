import AAG14CompletedInnerLift
import AAG15PhysicalFunctional
import AAG16FormBounds

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularVariational

open Grad.CartesianState

local instance annularZero_normedGroup (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    NormedAddCommGroup (annularInnerZero lower length positive bounded lengthPositive) := inferInstance

local instance annularZero_seminormedGroup (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    SeminormedAddCommGroup (annularInnerZero lower length positive bounded lengthPositive) :=
  (annularZero_normedGroup lower length positive bounded lengthPositive).toSeminormedAddCommGroup

instance annularInnerZero_complexInner (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    InnerProductSpace ℂ (annularInnerZero lower length positive bounded lengthPositive) :=
  Submodule.innerProductSpace (annularInnerZero lower length positive bounded lengthPositive)

instance annularInnerZero_realInner (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    InnerProductSpace ℝ (annularInnerZero lower length positive bounded lengthPositive) :=
  InnerProductSpace.rclikeToReal ℂ (annularInnerZero lower length positive bounded lengthPositive)

local instance annularZero_realNormedSpace (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    NormedSpace ℝ (annularInnerZero lower length positive bounded lengthPositive) :=
  (annularInnerZero_realInner lower length positive bounded lengthPositive).toNormedSpace

instance annularInnerZero_realModule (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    Module ℝ (annularInnerZero lower length positive bounded lengthPositive) :=
  (annularZero_realNormedSpace lower length positive bounded lengthPositive).toModule

def annularZeroInclusion (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    annularInnerZero lower length positive bounded lengthPositive →L[ℂ] annularEnergySpace lower length positive :=
  (annularInnerZero lower length positive bounded lengthPositive).subtypeL

def annularZeroRealInclusion (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    annularInnerZero lower length positive bounded lengthPositive →L[ℝ] annularEnergySpace lower length positive :=
  { toLinearMap :=
      { toFun := Subtype.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    cont := continuous_subtype_val }

private theorem annular_realCoercive_solution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (source : V →L[ℝ] ℝ) (test : V) :
    form (coercive.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual ℝ V).symm source)) test = source test := by
  have equality := coercive.continuousLinearEquivOfBilin_apply
    (coercive.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm source)) test
  rw [ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply] at equality
  exact equality.symm

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularZeroForm : annularInnerZero lower length positive bounded lengthPositive →L[ℝ]
    annularInnerZero lower length positive bounded lengthPositive →L[ℝ] ℝ := by
  let linear : annularInnerZero lower length positive bounded lengthPositive →ₗ[ℝ]
      annularInnerZero lower length positive bounded lengthPositive →L[ℝ] ℝ :=
    { toFun := fun field => (annularForm parameters lower length positive lengthPositive widthHalf widthLength field.val).comp
        (annularZeroRealInclusion lower length positive bounded lengthPositive)
      map_add' := fun first second => by
        apply ContinuousLinearMap.ext
        intro test
        exact congrArg (fun functional : annularEnergySpace lower length positive →L[ℝ] ℝ => functional test.val)
          ((annularForm parameters lower length positive lengthPositive widthHalf widthLength).map_add first.val second.val)
      map_smul' := fun scalar field => by
        apply ContinuousLinearMap.ext
        intro test
        exact congrArg (fun functional : annularEnergySpace lower length positive →L[ℝ] ℝ => functional test.val)
          ((annularForm parameters lower length positive lengthPositive widthHalf widthLength).map_smul scalar field.val)
    }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := annularInnerZero lower length positive bounded lengthPositive)
    (F := annularInnerZero lower length positive bounded lengthPositive →L[ℝ] ℝ)
    linear 4 (fun field => by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg field))
      intro test
      exact annularForm_abs_bound parameters lower length positive lengthPositive widthHalf widthLength field.val test.val)


theorem annularZeroForm_coercive_bound (field : annularInnerZero lower length positive bounded lengthPositive) :
    (3 / 4 : ℝ) * ‖field‖ ^ 2 ≤
      annularZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength field field := by
  change (3 / 4 : ℝ) * ‖field.val‖ ^ 2 ≤
    annularForm parameters lower length positive lengthPositive widthHalf widthLength field.val field.val
  exact annularForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength field.val

theorem annularZeroForm_isCoercive :
    IsCoercive (annularZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength) := by
  refine ⟨3 / 4, by norm_num, fun field => ?_⟩
  simpa only [sq, mul_assoc] using
    annularZeroForm_coercive_bound parameters lower length positive bounded lengthPositive widthHalf widthLength field

def annularVariationalRHS (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularInnerZero lower length positive bounded lengthPositive →L[ℝ] ℝ :=
  (annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source -
    annularForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularInnerLift lower length positive bounded innerValue)).comp
        (annularZeroRealInclusion lower length positive bounded lengthPositive)

def annularZeroSolution (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularInnerZero lower length positive bounded lengthPositive :=
  (annularZeroForm_isCoercive parameters lower length positive bounded lengthPositive widthHalf widthLength).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (annularInnerZero lower length positive bounded lengthPositive)).symm
      (annularVariationalRHS parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue))

theorem annularZeroSolution_real (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularZeroForm parameters lower length positive bounded lengthPositive widthHalf widthLength
      (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test =
      annularVariationalRHS parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue test :=
  annular_realCoercive_solution _
    (annularZeroForm_isCoercive parameters lower length positive bounded lengthPositive widthHalf widthLength) _ test

/-- The actual AG19 solution with independently prescribed inner value. -/
def annularVariationalSolution (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularEnergySpace lower length positive :=
  annularInnerLift lower length positive bounded innerValue +
    annularZeroInclusion lower length positive bounded lengthPositive
      (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)

theorem annularVariationalSolution_real (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test.val =
      annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  have law := annularZeroSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue test
  change annularForm parameters lower length positive lengthPositive widthHalf widthLength
      (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).val test.val =
    annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val -
      annularForm parameters lower length positive lengthPositive widthHalf widthLength
        (annularInnerLift lower length positive bounded innerValue) test.val at law
  unfold annularVariationalSolution
  rw [map_add, add_apply]
  change _ + annularForm parameters lower length positive lengthPositive widthHalf widthLength
    (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).val test.val = _
  linarith only [law]

theorem annularVariationalSolution_weak (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) test.val =
      annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  let solution := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have realLaw (point : annularInnerZero lower length positive bounded lengthPositive) :
      (annularFormValue parameters lower length positive lengthPositive widthHalf widthLength solution point.val).re =
        (annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val).re :=
    (annularForm_literal parameters lower length positive lengthPositive widthHalf widthLength solution point.val).symm.trans
      ((annularVariationalSolution_real parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue point).trans
        (annularFunctional_literal parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val))
  apply Complex.ext (realLaw test)
  have imaginaryLaw := realLaw (Complex.I • test)
  have formLaw := congrArg Complex.re
    (annularFormValue_test_smul parameters lower length positive lengthPositive widthHalf widthLength solution test.val Complex.I)
  have forcingLaw := congrArg Complex.re
    (annularFunctionalValue_test_smul parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val Complex.I)
  have equality := formLaw.symm.trans (imaginaryLaw.trans forcingLaw)
  simpa using equality

theorem annularVariationalSolution_inner (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularEnergyTrace lower length positive bounded lengthPositive 0
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) = innerValue := by
  unfold annularVariationalSolution
  rw [map_add, annularInnerLift_inner]
  have zero := (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue).property
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (annularZeroInclusion lower length positive bounded lengthPositive
      (annularZeroSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)) = 0 at zero
  rw [zero, add_zero]

end Inverse

end Grad.AnnularVariational
