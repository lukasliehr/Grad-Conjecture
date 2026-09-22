import AKCS3NativeOriginalRealForward
import AKBX2SameActualCurrentKernelParameters

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ActualPuncturedFamily
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.CompletedReality

/-- The actual fixed-reference physical current is real because its input
belongs to the original real state carrier. No current reality is assumed. -/
theorem actualPhysicalReference_currentReal (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    cartesianCoreConjugation parameters
      (physicalReferenceState parameters reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR base)).2.1=
      (physicalReferenceState parameters reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR base)).2.1 := by
  obtain ⟨axisReal,vectorReal,scalarReal⟩ := stateChart_real parameters reference insideR base.2
  rw [physicalReferenceState_formula]
  apply (normalizedChart_real seed insideS
    ((smoothingChartCore parameters base.2.val).1,
      toPhysicalCore parameters (Gauges.seedTransfer parameters reference insideR seed insideS base.2.val.2.1),
      base.2.val.2.2) axisReal axis ?_ scalarReal).1
  change cartesianCoreConjugation parameters (toPhysicalCore parameters
    (Gauges.seedTransfer parameters reference insideR seed insideS base.2.val.2.1))=_
  rw [toPhysicalCore_conjugate,Grad.ConstrainedTransfer.seedTransfer_conjugate,vectorReal]

end Grad.OriginalCoreRealization
