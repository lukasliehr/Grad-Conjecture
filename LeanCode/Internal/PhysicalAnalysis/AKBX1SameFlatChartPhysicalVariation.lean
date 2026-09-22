import AKBU21LiteralOriginalKernelConsumer
import AKAN4LiteralOriginalJetExhaustionConsumer
import QW4CoreEquivalence

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

theorem originalFlatDirection_axis_zero
    (flat : realChartKappa parameters reference insideR direction=0) : direction.val.1=0 := by
  apply Grad.FlatDomainProjection.smoothingToTangent_injective
  rw [map_zero]
  exact ((realChartKappa_eq_zero_iff reference insideR direction).mp flat).1

/-- The original physical first variation of a flat chart direction is the
same seed-transferred constrained pair, with the original Cartesian involution. -/
theorem originalFlatDirection_physical_first
    (flat : realChartKappa parameters reference insideR direction=0) :
    physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0,direction)) =
    (0,toPhysicalCore parameters
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.1,
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.2) := by
  have axisZero := originalFlatDirection_axis_zero parameters reference insideR direction flat
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

theorem zeroAxis_physicalStored_member
    (transferred : stateSmoothRange parameters seed insideS)
    (axisZero : transferred.val.1=0) :
    (0,toPhysicalCore parameters (toPhysicalCore parameters transferred.val.2.1),transferred.val.2.2)∈
        stateSmoothRange parameters seed insideS := by
  rw [toPhysicalCore_involutive,←axisZero]
  exact transferred.property

/-- The exact stored first variation is in the original seed's real constrained domain. -/
theorem originalFlatDirection_physical_member
    (flat : realChartKappa parameters reference insideR direction=0) :
    (0,toPhysicalCore parameters (toPhysicalCore parameters
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.1),
      (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.2)∈
        stateSmoothRange parameters seed insideS := by
  have formula := (constrainedCoreTransfer_coe parameters reference insideR seed insideS direction).trans
    (coreTransfer_apply parameters reference insideR seed insideS direction.val)
  have axis := congrArg (fun value : Grad.SmoothingFamily.StateCore parameters => value.1) formula
  exact zeroAxis_physicalStored_member parameters seed insideS
    (constrainedCoreTransfer parameters reference insideR seed insideS direction)
    (axis.trans (originalFlatDirection_axis_zero parameters reference insideR direction flat))

end Grad.OriginalCurrentInverseUniqueness
