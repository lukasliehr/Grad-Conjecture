import AKDS1ActualInverseTransposeProfile
import AKDR3SameAngularKernelField
import AKBL26SameWeightedOperatorFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.OriginalVectorCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.SourceCollar
open Grad.BoundaryTrace
open Grad.ActualCartesianWeakEquations Grad.GaugeCoefficients.Physical.RadialLedger

/-- A pointwise recovered original core represents exactly its SAME native
weighted full-cell field. The axis is removed only from an AE equality. -/
theorem originalCore_sameWeightedRep {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (raw : ℝ × Spatial → PhysicalValue dimension)
    (same : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) = raw (axial,point.val)) :
    StartupWeightedRep parameters.sigma0 parameters.gamma 1 (originalSourceMoments parameters core).field raw := by
  filter_upwards [originalSourceMoments_same parameters core,startupDisk_ae_nonzero,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point represented nonzero inside
  intro cell
  rw [represented cell]
  change cartesianWeight parameters cell point • originalCoreCell parameters core cell point =
    cartesianWeight parameters cell point • angularCoefficient (fun axial => raw (axial,point)) cell
  congr 1
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [← originalCoreCell_axialCoefficient parameters core cell closed]
  apply congrArg (fun function : ℝ → PhysicalValue dimension => angularCoefficient function cell)
  funext axial
  rw [show sourceCoreValue core closed axial =
    (originalPhysicalClosedJet parameters core).value (closed,(axial : CellCircle)) from
      sourceCoreValue_eq_originalPhysicalEvaluationLift core closed axial]
  exact same closed (norm_pos_iff.mpr nonzero) axial

/-- The physical product and its genuine original image core determine the
literal original weighted matrix action, ready for the sharp norm bound. -/
theorem originalCore_matrixField_fidelity {input output : ℕ} (parameters : PhaseParameters)
    (coefficients : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent coefficients) (core : ACore parameters input) (image : ACore parameters output)
    (raw : ℝ × Spatial → PhysicalValue input) (regular : StartupOrbitContinuous raw)
    (inputSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) = raw (axial,point.val))
    (outputSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters image).value (point,(axial : CellCircle)) =
        startupRawMatrix coefficients raw (axial,point.val)) :
    (originalSourceMoments parameters image).field =
      originalMatrixKernel (unitDiskAdmissible parameters) coefficients coherent
        (originalSourceMoments parameters core).field :=
  (originalCore_sameWeightedRep parameters image _ outputSame).ext
    ((originalCore_sameWeightedRep parameters core raw inputSame).matrix
      (unitDiskAdmissible parameters) coefficients coherent regular)

end Grad.OriginalVectorCoreRecovery
