import AKCF2OrdinaryFullCellCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.NativePuncturedGraph
open Grad.ClosedJets Grad.CartesianState Grad.CartesianCoreRecovery Grad.PDEBootstrap
open Grad.GenericCarriers Grad.CartesianStartup Grad.CellWeights Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeakTesting

private theorem pairing_selected {dimension : ℕ} (field : StartupL2 dimension) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk) :
    testPairing dimension openUnitDisk cell vector test field=
      apDiskPairing dimension 0 vector test.toFun test.smooth test.compact (fieldCellProjection dimension openUnitDisk cell field) := by
  rw [testPairing,apDiskPairing,ContinuousLinearMap.comp_apply,compactPairing_apply,compactPairing_apply]
  apply integral_congr_ae
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk field,
    apDiskInjection_ae (fieldCellProjection dimension openUnitDisk cell field)] with point projection injected
  rw [injected,cellSingle_apply,if_pos rfl,projection cell]

private theorem derivativePairing_selected {dimension order : ℕ} (field : StartupL2 dimension) (index : JetIndex order) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk) :
    derivativeTestPairing dimension order openUnitDisk index cell vector test field=
      apDiskDerivativePairing dimension 0 vector test.toFun test.smooth test.compact (degree index) (derivativeWord index)
        (fieldCellProjection dimension openUnitDisk cell field) := by
  rw [derivativeTestPairing,apDiskDerivativePairing,ContinuousLinearMap.comp_apply,orderedDerivativePairing_apply,orderedDerivativePairing_apply]
  apply integral_congr_ae
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk field,
    apDiskInjection_ae (fieldCellProjection dimension openUnitDisk cell field)] with point projection injected
  rw [injected,cellSingle_apply,if_pos rfl,projection cell]

private theorem closedMultiDerivative_origin {dimension : ℕ} (field : ClosedJet dimension) :
    closedMultiDerivative field (0,0)=field.value := by
  have word : cartesianMultiIndexWord (0,0)=emptyCartesianWord := by
    funext position
    exact Fin.elim0 position
  change closedDerivative field 0 (cartesianMultiIndexWord (0,0))=field.value
  rw [word,closedDerivative_zero_order]

variable {dimension : ℕ} (field : OrdinaryCoefficientCore dimension)

/-- Every literal ordinary coefficient core supplies genuine complete-cell
weak graphs at every spatial order and every cell power. -/
def ordinaryAllOrderGraph (order weight : ℕ) : GraphGrade dimension order weight openUnitDisk :=
  ofCoordinates dimension order openUnitDisk (fun _ => weight)
    (fun index => ordinaryDerivativeJoint field weight index.val) (by
      intro index cell vector test
      rw [ordinaryDerivativeJoint_inverse, pairing_selected,ordinaryDerivativeJoint_coordinate,
        derivativePairing_selected,ordinaryDerivativeJoint_coordinate]
      change apDiskPairing dimension 0 vector test.toFun test.smooth test.compact
          ((cellFrequency cell : ℂ)^weight • closedContinuousToDiskL2
            (closedDerivative (field.val cell) (degree index) (derivativeWord index)))=
        ((-1 : ℂ)^degree index*positiveFactor weight cell)*
          apDiskDerivativePairing dimension 0 vector test.toFun test.smooth test.compact (degree index) (derivativeWord index)
            ((cellFrequency cell : ℂ)^0 • closedContinuousToDiskL2 (closedMultiDerivative (field.val cell) (0,0)))
      rw [map_smul,apClosedJet_weak (field.val cell) (derivativeWord index) 0 vector test.toFun test.smooth test.compact test.supported]
      simp only [pow_zero,one_smul,closedMultiDerivative_origin]
      change (cellFrequency cell : ℂ)^weight*((-1 : ℂ)^degree index*_) =
        ((-1 : ℂ)^degree index*(cellFrequency cell : ℂ)^weight)*_
      ring)

theorem ordinaryAllOrderGraph_base (order weight : ℕ) :
    base dimension order openUnitDisk (fun _ => weight) (ordinaryAllOrderGraph field order weight)=
      ordinaryDerivativeJoint field 0 (0,0) :=
  ordinaryDerivativeJoint_inverse field weight (0,0)

theorem ordinaryAllOrderGraph_same (order weight : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base dimension order openUnitDisk (fun _ => weight) (ordinaryAllOrderGraph field order weight) point cell=
        closedDiskLift (field.val cell).value point := by
  rw [ordinaryAllOrderGraph_base]
  filter_upwards [ordinaryDerivativeJoint_same field 0 (0,0)] with point same
  intro cell
  simpa only [pow_zero,one_smul,closedMultiDerivative_origin] using same cell

end Grad.NativePuncturedGraph
