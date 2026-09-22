import AKDP58ActualLedgerPrincipalEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.OriginalCartesianTameEstimate
open Grad.CartesianCoreRecovery Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation Grad.NonlinearProduct Grad.CellWeights

theorem startupRecoveredMixed_originalCore {dimension order : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order openUnitDisk exponent)
    (same : base dimension order openUnitDisk exponent jet=(originalSourceMoments parameters core).field)
    (index : JetIndex order) :
    Realization.recoveredDerivative dimension order openUnitDisk exponent index jet=
      originalSourceOrderedJoint parameters core (degree index) (derivativeWord index) := by
  have actual := recoveredDerivative_hasWeak dimension order openUnitDisk exponent index jet
  rw [same] at actual
  exact weakEquality dimension openUnitDisk openUnitDisk_isOpen (degree index) (derivativeWord index)
    (derivativeWord index) (fun _ => rfl) _ _ _ actual
    (originalSourceOrderedJoint_weak parameters core (degree index) (derivativeWord index))

/-- Every genuine mixed graph of the same original field has exactly its
original ACore norm, independently of how the graph was constructed. -/
theorem startupOriginalMixedNorm_eq_graph {dimension grade : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : Mixed dimension grade openUnitDisk)
    (same : base dimension grade openUnitDisk (fun index => grade-degree index) jet=(originalSourceMoments parameters core).field) :
    originalGradeNorm grade core=‖jet‖ := by
  change ‖GradeCore.ofCoreLinear (grade := grade) core‖=‖jet‖
  apply originalCore_norm_eq_mixed parameters core jet
  intro cell index
  let target := originalJetIndexEquiv grade index
  have derivative := startupRecoveredMixed_originalCore parameters core (fun index => grade-degree index) jet same target
  have positive := Realization.recoveredDerivative_positive_coordinates dimension grade openUnitDisk
    (fun index => grade-degree index) target jet
  have coordinate : fieldCellProjection dimension openUnitDisk cell (jet.val target)=
      (cellFrequency cell : ℂ)^(grade-degree target) •
        originalSourceOrderedCoordinate parameters core (degree target) (derivativeWord target) cell := by
    apply Lp.ext
    filter_upwards [fieldCellProjection_ae dimension openUnitDisk (jet.val target),positive,
      fieldCellProjection_ae dimension openUnitDisk (originalSourceOrderedJoint parameters core (degree target) (derivativeWord target)),
      Lp.coeFn_smul ((cellFrequency cell : ℂ)^(grade-degree target))
        (originalSourceOrderedCoordinate parameters core (degree target) (derivativeWord target) cell)]
      with point projected stored original scaled
    rw [projected cell,stored cell,derivative]
    have originalCell := original cell
    have coordinateAt := congrArg (fun field : DiskL2 dimension => field point)
      (originalSourceOrderedJoint_coordinate parameters core (degree target) (derivativeWord target) cell)
    rw [coordinateAt] at originalCell
    rw [scaled,Pi.smul_apply,originalCell]
    simp only [positiveFactor,cellFrequency]
  rw [coordinate]
  rfl

end Grad.CartesianStartup
