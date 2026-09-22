import ANL7CircularBoundaryGrade
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus
local instance (priority := 2000) normalUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) :=
  unitNormedSpace grade
local instance (priority := 2000) normalBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

local instance normalLiftUnitComplete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

def normalModeJetLinear (mode : ℤ) : ComplexEuclidean 1 →ₗ[ℂ] ClosedJet 1 where
  toFun value := globalClosedJet (fun point => normalKernel mode point • value)
    ((normalKernel_smooth mode).smul contDiff_const)
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_add _ _ _
  map_smul' scalar value := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_comm _ _ _

def finiteNormalLinear : NormalFiniteData →ₗ[ℂ] ClosedJet 1 :=
  Finsupp.lsum ℂ normalModeJetLinear

theorem finiteNormalLinear_eq (values : NormalFiniteData) :
    finiteNormalLinear values = finiteNormalJet values.support values := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change jetValueLinear point (finiteNormalLinear values) = _
  rw [finiteNormalLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  rfl

def finiteNormalInto (grade : ℕ) : NormalFiniteData →ₗ[ℂ] unitDiskSobolev grade :=
  (unitDiskCoreInto grade).comp finiteNormalLinear

theorem finiteNormalInto_bound (grade : ℕ) (gradeBound : 2 ≤ grade) (values : NormalFiniteData) :
    ‖finiteNormalInto grade values‖ ≤
      Real.sqrt (normalSobolevConstant grade) * ‖normalBoundaryInto grade values‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (normalSobolevConstant_nonnegative grade), normalBoundaryInto_norm_sq grade gradeBound]
  change ‖unitDiskCoreInto grade (finiteNormalLinear values)‖ ^ 2 ≤ _
  have equality := congrArg (fun core : ClosedJet 1 => ‖unitDiskCoreInto grade core‖ ^ 2)
    (finiteNormalLinear_eq values)
  exact equality.le.trans (finiteNormalJet_norm_sq values.support values grade gradeBound)

/-- The actual completed normal coretraction into ordinary disk H^q. -/
def completedNormalLift (grade : ℕ) : normalBoundaryGrade grade →L[ℂ] unitDiskSobolev grade :=
  (finiteNormalInto grade).extendOfNorm (normalBoundaryInto grade)

theorem completedNormalLift_finite (grade : ℕ) (gradeBound : 2 ≤ grade) (values : NormalFiniteData) :
    completedNormalLift grade (normalBoundaryInto grade values) =
      unitDiskCoreInto grade (finiteNormalLinear values) :=
  LinearMap.extendOfNorm_eq (normalBoundaryInto_denseRange grade)
    ⟨Real.sqrt (normalSobolevConstant grade), finiteNormalInto_bound grade gradeBound⟩ values

private theorem extension_norm_bound {Core Source Target : Type*}
    [AddCommGroup Core] [Module ℂ Core] [NormedAddCommGroup Source] [NormedSpace ℂ Source]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]
    (inclusion : Core →ₗ[ℂ] Source) (dense : DenseRange inclusion) (mapping : Core →ₗ[ℂ] Target)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bounded : ∀ core, ‖mapping core‖ ≤ constant * ‖inclusion core‖) :
    ‖mapping.extendOfNorm inclusion‖ ≤ constant :=
  LinearMap.opNorm_extendOfNorm_le dense nonnegative bounded

private theorem map_bound {Source Target : Type*}
    [NormedAddCommGroup Source] [NormedSpace ℂ Source]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (mapping : Source →L[ℂ] Target) (constant : ℝ) (bounded : ‖mapping‖ ≤ constant) (field : Source) :
    ‖mapping field‖ ≤ constant * ‖field‖ := mapping.le_of_opNorm_le bounded field

theorem completedNormalLift_norm_le (grade : ℕ) (gradeBound : 2 ≤ grade) :
    ‖completedNormalLift grade‖ ≤ Real.sqrt (normalSobolevConstant grade) := by
  exact @extension_norm_bound NormalFiniteData (normalBoundaryGrade grade) (unitDiskSobolev grade)
    inferInstance inferInstance inferInstance (normalBoundarySpace grade)
    inferInstance (unitNormedSpace grade) (normalLiftUnitComplete grade)
    (normalBoundaryInto grade) (normalBoundaryInto_denseRange grade) (finiteNormalInto grade)
    (Real.sqrt (normalSobolevConstant grade)) (Real.sqrt_nonneg _) (finiteNormalInto_bound grade gradeBound)

theorem completedNormalLift_bound (grade : ℕ) (gradeBound : 2 ≤ grade)
    (field : normalBoundaryGrade grade) :
    ‖completedNormalLift grade field‖ ≤ Real.sqrt (normalSobolevConstant grade) * ‖field‖ :=
  @map_bound (normalBoundaryGrade grade) (unitDiskSobolev grade)
    inferInstance (normalBoundarySpace grade) inferInstance (unitNormedSpace grade)
    (completedNormalLift grade) _ (completedNormalLift_norm_le grade gradeBound) field

end Grad.CircularNormalLift
