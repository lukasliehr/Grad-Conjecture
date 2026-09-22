import AKCW5FixedCollarEvaluation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : CompactSpace PhysicalCollar := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_closedBall (0 : SpatialPlane) (4/3 : ℝ)

variable {dimension : ℕ} (parameters : PhaseParameters)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

def originalPacketParameterDerivative (order : ℕ) (field : Parameter → ACore parameters dimension)
    (point : Parameter) : Parameter →L[ℝ]
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
  ((completedOriginalCollarDerivative (dimension := dimension) parameters order).restrictScalars ℝ).comp
    (fderiv ℝ (completedCoreBranch parameters field (order+3)) point)

theorem originalPacketParameterDerivative_hasFDerivAt (order : ℕ)
    (field : Parameter → ACore parameters dimension) (point : Parameter)
    (differentiable : DifferentiableAt ℝ (completedCoreBranch parameters field (order+3)) point) :
    HasFDerivAt (fun input => originalCollarDerivative parameters order (field input))
      (originalPacketParameterDerivative parameters order field point) point := by
  let packetMap : AGrade parameters dimension (order+3) →L[ℝ]
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
    (completedOriginalCollarDerivative (dimension := dimension) parameters order).restrictScalars ℝ
  have mapDerivative : HasFDerivAt packetMap packetMap
      (completedCoreBranch parameters field (order+3) point) := packetMap.hasFDerivAt
  have derivative : HasFDerivAt (fun input => packetMap (completedCoreBranch parameters field (order+3) input))
      (packetMap.comp (fderiv ℝ (completedCoreBranch parameters field (order+3)) point)) point :=
    @HasFDerivAt.comp ℝ inferInstance Parameter inferInstance inferInstance
      (AGrade parameters dimension (order+3)) inferInstance inferInstance
      C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension)
      inferInstance inferInstance _ _ point packetMap packetMap mapDerivative differentiable.hasFDerivAt
  change HasFDerivAt (fun input => completedOriginalCollarDerivative parameters order
    (aGradeEta parameters (GradeCore.ofCoreLinear (field input)))) _ _ at derivative
  simpa only [completedOriginalCollarDerivative_core, packetMap, originalPacketParameterDerivative] using derivative

def originalClampedParameterDerivative (order : ℕ) (field : Parameter → ACore parameters dimension)
    (parameter : Parameter) (point : SpatialCell) :
    Parameter →L[ℝ] SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  (ContinuousMap.evalCLM ℝ (fixedCollarPoint point)).comp
    (originalPacketParameterDerivative parameters order field parameter)

theorem originalClampedParameterDerivative_hasFDerivAt (order : ℕ)
    (field : Parameter → ACore parameters dimension) (parameter : Parameter) (point : SpatialCell)
    (differentiable : DifferentiableAt ℝ (completedCoreBranch parameters field (order+3)) parameter) :
    HasFDerivAt (fun input => originalClampedDerivative parameters order (field input) point)
      (originalClampedParameterDerivative parameters order field parameter point) parameter := by
  let evaluate : C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension := ContinuousMap.evalCLM ℝ (fixedCollarPoint point)
  have outer : HasFDerivAt evaluate evaluate (originalCollarDerivative parameters order (field parameter)) := evaluate.hasFDerivAt
  exact @HasFDerivAt.comp ℝ inferInstance Parameter inferInstance inferInstance
    C(PhysicalCollarDomain, SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) inferInstance inferInstance
    (SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) inferInstance inferInstance
    _ _ parameter evaluate evaluate outer
    (originalPacketParameterDerivative_hasFDerivAt parameters order field parameter differentiable)

theorem originalClampedParameterDerivative_direction {domain : Set Parameter}
    (openDomain : IsOpen domain) (order : ℕ) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (parameter : Parameter) (member : parameter∈domain) (point : SpatialCell) (direction : Parameter) :
    originalClampedParameterDerivative parameters order field parameter point direction=
      originalClampedDerivative parameters order
        (originalParameterDirectionField parameters openDomain field smooth direction parameter) point := by
  change completedOriginalCollarDerivative parameters order
      (fderiv ℝ (completedCoreBranch parameters field (order+3)) parameter direction) (fixedCollarPoint point)=
    originalCollarDerivative parameters order
      (originalParameterDirectionField parameters openDomain field smooth direction parameter) (fixedCollarPoint point)
  rw [← originalParameterDirectionField_component parameters openDomain field smooth direction parameter member (order+3)]
  unfold completedCoreBranch
  rw [completedOriginalCollarDerivative_core]

theorem originalClampedParameterDerivative_continuous [FiniteDimensional ℝ Parameter]
    {domain : Set Parameter} (openDomain : IsOpen domain) (order : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContinuousOn (fun point : Parameter × SpatialCell =>
      originalClampedParameterDerivative parameters order field point.1 point.2) (domain ×ˢ univ) := by
  apply continuousOn_clm_apply.mpr
  intro direction
  have continuous := originalClampedDerivative_joint_continuous parameters order
    (originalParameterDirectionField parameters openDomain field smooth direction)
    (originalParameterDirectionField_completed_smooth parameters openDomain field smooth direction (order+3))
  exact continuous.congr (fun point member =>
    originalClampedParameterDerivative_direction parameters openDomain order field smooth point.1 member.1 point.2 direction)

omit [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter] in
theorem originalClampedDerivative_spatial (order : ℕ) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈originalOpenCollar) :
    HasFDerivAt (originalClampedDerivative parameters order field)
      (originalClampedDerivative parameters (order+1) field point).curryLeft point := by
  rw [originalClampedDerivative_same parameters (order+1) field point inside]
  apply (ambientHigherDerivative_hasFDerivAt (originalPhysicalClosedJet parameters field) order point).congr_of_eventuallyEq
  filter_upwards [originalOpenCollar_isOpen.mem_nhds inside] with nearby member
  exact originalClampedDerivative_same parameters order field nearby member

end Grad.OriginalParameterEvaluation
