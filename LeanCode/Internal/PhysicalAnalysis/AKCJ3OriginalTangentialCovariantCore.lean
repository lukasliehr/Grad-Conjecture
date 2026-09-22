import AKCJ2OriginalSourcedCovariantThird
import AKCA22LiteralScalarPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal polynomial tangential component of the original full-frame core. -/
theorem originalTangentialCovariant_core (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) :
    dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) vector=
      coordinateCore parameters 0
        (valueMapCore parameters (matrixUnit (0 : Fin 1) (1 : Fin 3))
          (originalCovariantCore parameters length epsilon base vector false))-
      coordinateCore parameters 1
        (valueMapCore parameters (matrixUnit (0 : Fin 1) (0 : Fin 3))
          (originalCovariantCore parameters length epsilon base vector false)) := by
  rw [originalCovariantCore,originalScalarTripletCore_coordinate,originalScalarTripletCore_coordinate]
  simp only [Bool.false_eq_true,if_false,originalFrameColumnCore,Matrix.cons_val]
  simp only [rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,dot_coordinate_first]

/-- Pointwise fidelity uses the genuine original core, including all axial cells. -/
theorem originalTangentialCovariant_value (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (point : ClosedDisk) (axial : ℝ) :
    coreValue (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) vector) point axial=
      scalarTangentialPolynomial point.val
        (coreValue (originalCovariantCore parameters length epsilon base vector false) point axial) := by
  rw [originalTangentialCovariant_core parameters length epsilon base vector,Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract,coreValue_coordinate,coreValue_coordinate,
    coreValue_valueMap,coreValue_valueMap]
  rfl

end Grad.OriginalCoreRealization
