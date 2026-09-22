import AKCU1OriginalZeroAxisFirstVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace Grad.OriginalCurrentInverseUniqueness
open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.ConstrainedTransfer Grad.ChartAxisProjections Grad.ChartAxisLift
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization

variable (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
  (vector : ACore parameters 3) (scalar : ACore parameters 1)
  (member : (0,toPhysicalCore parameters vector,scalar)∈stateSmoothRange parameters seed insideS)

/-- The exact inverse seed transfer of the SAME stored physical pair. -/
def originalPairReferenceState : stateSmoothRange parameters reference insideR :=
  (coreTransferEquiv parameters reference insideR seed insideS).symm ⟨(0,toPhysicalCore parameters vector,scalar),member⟩

theorem originalPairReferenceState_transfer :
    constrainedCoreTransfer parameters reference insideR seed insideS
      (originalPairReferenceState parameters reference insideR seed insideS vector scalar member)=
        ⟨(0,toPhysicalCore parameters vector,scalar),member⟩ :=
  (coreTransferEquiv parameters reference insideR seed insideS).apply_symm_apply _

theorem originalPairReferenceState_axis :
    (originalPairReferenceState parameters reference insideR seed insideS vector scalar member).val.1=0 := rfl

/-- The actual fixed-reference derivative of this inverse-transferred pair is
literally the original physical derivative on SAME U/S. -/
theorem originalPairReferenceState_forward (length : ℝ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    (literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis
      (originalPairReferenceState parameters reference insideR seed insideS vector scalar member)).val=
    quotientRowsDerivative parameters length 1
      (physicalReferenceState parameters reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR base)) ![(0,vector,scalar)] := by
  change literalPhysicalSmoothForwardRows parameters length reference insideR seed insideS base _=_
  unfold literalPhysicalSmoothForwardRows
  rw [originalZeroAxisDirection_physical_first parameters reference insideR seed insideS base _
    (originalPairReferenceState_axis parameters reference insideR seed insideS vector scalar member),
    originalPairReferenceState_transfer,toPhysicalCore_involutive]
  congr 1
  funext coordinate
  fin_cases coordinate
  rfl

end Grad.OriginalCurrentInverseUniqueness
