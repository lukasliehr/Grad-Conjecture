import AKCS5ActualChartNativeRealForward
import AKBX6ActualOriginalTwoSidedAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option maxRecDepth 4000
namespace Grad.OriginalCurrentInverseUniqueness
open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.ConstrainedTransfer Grad.ChartAxisProjections Grad.ChartAxisLift
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization

variable (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
  (base : RealJointCore parameters reference insideR)
  (direction : stateSmoothRange parameters reference insideR)

/-- The original physical first variation of a flat chart direction is the
same seed-transferred constrained pair, with the original Cartesian involution. -/
theorem originalZeroAxisDirection_physical_first
    (axisZero : direction.val.1=0) :
    physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0,direction)) =
    (0,toPhysicalCore parameters
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.1,
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.2) := by
  have chart : physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (smoothingChartCore parameters direction.val) =
      (0,toPhysicalCore parameters
        (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.1,
        (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.2) := by
    apply Prod.ext
    · change smoothingToTangent parameters direction.val.1=0
      rw [axisZero,map_zero]
    · rfl
  apply Prod.ext
  · rfl
  · change chartDerivativeFamily parameters seed insideS 1 _
      (fun _ => physicalFixedReferenceTransfer parameters reference insideR seed insideS
        (smoothingChartCore parameters direction.val))=_
    rw [chart,chartDerivativeFamily_one_root,rootDerivativeFamily_one_zero,chartAffineField_zero_inputs]


end Grad.OriginalCurrentInverseUniqueness
