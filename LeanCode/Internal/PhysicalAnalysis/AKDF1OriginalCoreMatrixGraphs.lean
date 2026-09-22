import AKCX30SameOriginalSourceAllOrder
import AKBT2ActualNativeWeightedRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.OriginalVectorCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup
open Grad.WeightedJets Grad.SpatialDilation Grad.ActualOriginalSourceFirst Grad.ActualScalarWeakEquations
open Grad.SourceCollar
open Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.NonlinearRange
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnalyticWeights.Calculus

/-- A coherent original coefficient matrix acts on an actual original core
at every spatial and cell grade, preserving its literal physical product. -/
theorem originalCore_matrix_allGraphs {input output : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters input)
    (coefficients : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent coefficients)
    (raw : ℝ × Spatial → PhysicalValue input) (regular : StartupOrbitContinuous raw)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) = raw (axial,point.val)) :
    ∃ field : StartupL2 output,
      (∀ grade, ∃ graph : GraphGrade output grade grade openUnitDisk,
        base output grade openUnitDisk (fun _ => grade) graph = field) ∧
      StartupWeightedRep parameters.sigma0 parameters.gamma 1 field (startupRawMatrix coefficients raw) := by
  let scale : Scale := ⟨1,by norm_num⟩
  let source := (StartupSignedFirstFamily.source parameters core 1 scale).toStartupSignedFamily
  let result := source.matrix (unitDiskAdmissible parameters) coefficients coherent
  have sourceSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 source.field raw := by
    filter_upwards [scaledOriginalSourceFirst_same parameters core scale,
      startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point represented nonzero inside
    intro cell
    change base input 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters core scale) point cell = _
    have cells := represented cell
    simp only [scale,one_smul] at cells
    rw [cells]
    congr 1
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    rw [← originalCoreCell_axialCoefficient parameters core cell closed]
    apply congrArg (fun function : ℝ → PhysicalValue input => angularCoefficient function cell)
    funext axial
    rw [show sourceCoreValue core closed axial =
      (originalPhysicalClosedJet parameters core).value (closed,(axial : CellCircle)) from
      sourceCoreValue_eq_originalPhysicalEvaluationLift core closed axial]
    exact same closed (norm_pos_iff.mpr nonzero) axial
  refine ⟨result.field,?_,sourceSame.matrix (unitDiskAdmissible parameters) coefficients coherent regular⟩
  intro grade
  have inputRegular := StartupSignedFirstFamily.source_allSpatialGrade parameters core 1 one_ne_zero scale grade
  have outputRegular := inputRegular.matrix (unitDiskAdmissible parameters) coefficients coherent one_ne_zero one_ne_zero
  obtain ⟨graph,graphSame⟩ := outputRegular 0 grade
  exact ⟨graph,graphSame.trans result.zero⟩

end Grad.OriginalVectorCoreRecovery
