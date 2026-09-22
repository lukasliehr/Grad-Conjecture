import AXP1PhysicalExtraction

noncomputable section

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RawForward
open Grad.NonlinearRange Grad.QuotientProjection Grad.Q24Realization Grad.RealFixedRanges

variable {parameters : PhaseParameters}

theorem physicalReferenceState_realCore_gauge
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) :
    GaugeState parameters (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state)) := by
  apply normalizedChart_mean_zero
  exact (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR state.2).2

def rawPhysicalFixedSliceCore (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) : QuotientRows parameters :=
  originalRawRowsCore parameters cellLength
    (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state))

/-- The literal four raw equations on the corrected physical chart.
This is a whole-closed-disk identity, not division on a punctured domain. -/
theorem rawPhysicalFixedSliceCore_identity (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) :
    rawReconstructionCore parameters (physicalFixedSliceMap parameters cellLength reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state)) =
      rawPhysicalFixedSliceCore parameters cellLength reference insideR seed insideS state :=
  rawReconstruction_polynomial cellLength _ (physicalReferenceState_realCore_gauge reference insideR seed insideS state)

end Grad.PhysicalCoordinates
