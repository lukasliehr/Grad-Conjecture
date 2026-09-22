import QX5RawBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.RawForward

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.Q24Realization Grad.RealFixedRanges

variable {parameters : PhaseParameters}

/-- All four original rows, not a projected replacement of the residual. -/
theorem rawReconstruction_polynomial (cellLength : ℝ) (state : QuotientState parameters)
    (gauge : GaugeState parameters state) :
    rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state) =
      originalRawRowsCore parameters cellLength state := by
  funext index
  fin_cases index
  · exact rawReconstruction_first cellLength state
  · exact rawReconstruction_second cellLength state gauge
  · exact rawReconstruction_third cellLength state
  · exact rawReconstruction_fourth cellLength state

theorem referenceState_gauge (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (state : JointState parameters)
    (scalarMean : angularCore parameters 0 state.2.2.2 = 0) :
    GaugeState parameters (referenceState parameters reference insideR seed insideS state) := by
  exact normalizedChart_mean_zero seed insideS
    (referenceTransfer parameters reference insideR seed insideS state.2) scalarMean

theorem referenceState_realCore_gauge (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) :
    GaugeState parameters (referenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state)) :=
  referenceState_gauge reference insideR seed insideS _
    (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR state.2).2

/-- Literal four raw equations evaluated at the actual fixed-reference
chart, retaining its N18 transfer, root chart and scalar normalization. -/
def rawFixedSliceCore (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) : QuotientRows parameters :=
  originalRawRowsCore parameters cellLength
    (referenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state))

theorem rawFixedSliceCore_identity (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) :
    rawReconstructionCore parameters (fixedSliceMap parameters cellLength reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR state)) =
      rawFixedSliceCore parameters cellLength reference insideR seed insideS state :=
  rawReconstruction_polynomial cellLength _ (referenceState_realCore_gauge reference insideR seed insideS state)

theorem realJointCoreToJoint_state_line (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) (scalar : ℝ) :
    realJointCoreToJoint parameters reference insideR (base.1, base.2 + scalar • direction) =
      realJointCoreToJoint parameters reference insideR base +
        (scalar : ℂ) • realJointCoreToJoint parameters reference insideR (0, direction) := by
  apply Prod.ext
  · change (base.1 : ℂ) = (base.1 : ℂ) + (scalar : ℂ) • (0 : ℂ)
    rw [smul_zero, add_zero]
  · rfl

end Grad.RawForward
