import AKCW1SameOriginalCollarExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : CompactSpace PhysicalCollar := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_closedBall (0 : SpatialPlane) (4 / 3 : ℝ)

variable {dimension : ℕ} (parameters : PhaseParameters)

/-- All actual spatial derivatives of the SAME field on the fixed collar. -/
def originalCollarDerivative (order : ℕ) (field : ACore parameters dimension) :
    C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
  collarPhysicalOperatorDerivative (periodizedExtension (originalPhysicalClosedJet parameters field)) order

theorem originalCollarDerivative_apply (order : ℕ) (field : ACore parameters dimension)
    (point : PhysicalCollarDomain) :
    originalCollarDerivative parameters order field point =
      iteratedFDeriv ℝ order (originalExtendedField parameters field)
        (assembleSpatialCell point.1.val (physicalCellRepresentative point.2)) := by
  change torusPhysicalOperatorDerivative (periodizedExtension (originalPhysicalClosedJet parameters field)) order
    (physicalCollarToTorus point)=_
  rw [torusPhysicalOperatorDerivative_periodized_at_collar,
    ambientHigherDerivative_eq_iteratedFDeriv_ambient]
  rfl

def originalCollarDerivativeLinear (order : ℕ) :
    ACore parameters dimension →ₗ[ℂ]
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) where
  toFun := originalCollarDerivative parameters order
  map_add' first second := by
    ext point : 1
    change originalCollarDerivative parameters order (first+second) point =
      originalCollarDerivative parameters order first point + originalCollarDerivative parameters order second point
    simp only [originalCollarDerivative_apply, originalExtendedField_add]
    exact iteratedFDeriv_add_apply
      ((originalExtendedField_smooth parameters first).of_le (by exact_mod_cast le_top)).contDiffAt
      ((originalExtendedField_smooth parameters second).of_le (by exact_mod_cast le_top)).contDiffAt
  map_smul' scalar field := by
    ext point : 1
    change originalCollarDerivative parameters order (scalar • field) point =
      scalar • originalCollarDerivative parameters order field point
    simp only [originalCollarDerivative_apply, originalExtendedField_smul]
    exact iteratedFDeriv_const_smul_apply
      ((originalExtendedField_smooth parameters field).of_le (by exact_mod_cast le_top)).contDiffAt

def originalCollarDerivativeConstant (order : ℕ) : ℝ :=
  physicalExtensionCNormFactor order * originalPhysicalEvaluationConstant parameters order

theorem originalCollarDerivative_bound (order : ℕ)
    (field : GradeCore parameters dimension (order+3)) :
    ‖originalCollarDerivative parameters order field.toCore‖ ≤
      originalCollarDerivativeConstant parameters order * ‖field‖ := by
  exact (collarPhysicalOperatorDerivative_norm_bound
    (originalPhysicalClosedJet parameters field.toCore) (le_refl order)).trans
    ((mul_le_mul_of_nonneg_left
      (originalField_closedPhysicalCNorm_bound parameters field)
      (physicalExtensionCNormFactor_nonnegative order)).trans_eq (mul_assoc _ _ _).symm)

/-- Only the complete continuous-map packet is extended to the completion. -/
def completedOriginalCollarDerivative (order : ℕ) :
    AGrade parameters dimension (order+3) →L[ℂ]
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
  denseCoreExtension (dimension := dimension) (grade := order+3) parameters
    (Target := C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension))
    ((originalCollarDerivativeLinear parameters order).comp GradeCore.toCoreLinear)
    (originalCollarDerivativeConstant parameters order)
    (by intro field; exact originalCollarDerivative_bound parameters order field)

theorem completedOriginalCollarDerivative_core (order : ℕ)
    (field : ACore parameters dimension) :
    completedOriginalCollarDerivative parameters order
      (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      originalCollarDerivative parameters order field :=
  by
    unfold completedOriginalCollarDerivative
    erw [denseCoreExtension_apply_eta]
    rfl

/-- Smoothness of the exact spatial-derivative packet follows from the
original completed grade, with the fixed three-derivative evaluation loss. -/
theorem originalCollarDerivative_parameter_smooth
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    {domain : Set Parameter} {order : ℕ} (field : Parameter → ACore parameters dimension)
    (smooth : ContDiffOn ℝ ∞ (fun point =>
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := order+3) (field point))) domain) :
    ContDiffOn ℝ ∞ (fun point => originalCollarDerivative parameters order (field point)) domain := by
  let packetMap : AGrade parameters dimension (order+3) →L[ℝ]
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
    (completedOriginalCollarDerivative parameters order).restrictScalars ℝ
  have packetSmooth : ContDiff ℝ ∞ packetMap :=
    @ContinuousLinearMap.contDiff ℝ
      (AGrade parameters dimension (order+3))
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension)
      inferInstance inferInstance inferInstance inferInstance inferInstance ∞ packetMap
  have composed := packetSmooth.comp_contDiffOn smooth
  change ContDiffOn ℝ ∞ (fun point =>
    completedOriginalCollarDerivative parameters order
      (aGradeEta parameters (GradeCore.ofCoreLinear (field point)))) domain at composed
  simpa only [ContinuousLinearMap.coe_restrictScalars, Function.comp_apply,
    completedOriginalCollarDerivative_core] using composed

end Grad.OriginalParameterEvaluation
