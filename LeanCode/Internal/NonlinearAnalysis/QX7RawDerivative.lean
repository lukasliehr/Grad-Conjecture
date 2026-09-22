import QX6RawCoreIdentity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.RawForward

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.Q24Realization Grad.RealFixedRanges
open Grad.SmoothForward

/-- Applying the literal reconstruction to the constructed smooth forward
operator gives the genuine derivative of all four original raw equations,
through the actual fixed-reference chart. The equality holds in every
original grade, on the whole closed disk; it invokes no inverse division. -/
theorem literalSmoothForward_rawDerivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    HasDerivAt
      (fun scalar : ℝ => quotientEta parameters grade
        (rawFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction)))
      (quotientEta parameters grade (rawReconstructionCore parameters
        (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction).val)) 0 := by
  let joint := realJointCoreToJoint parameters reference insideR base
  let jointDirection := realJointCoreToJoint parameters reference insideR (0, direction)
  have genuine : IsJointRowsDirectionalDerivative
      (fixedSliceMap parameters cellLength reference insideR seed insideS) joint jointDirection
      (literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction) := by
    have step := composedDerivative_genuine (referenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun order base directions admissible =>
        referenceFamily_genuine reference insideR seed insideS order base directions admissible)
      cellLength 0 joint (fun _ => jointDirection) axis
    simp only [composedDerivative_zeroth, referenceFamily_zeroth] at step
    convert step using 1 <;> rfl
  have derivative := coreRows_hasDerivAt parameters grade
    (fun point => rawReconstructionCore parameters
      (fixedSliceMap parameters cellLength reference insideR seed insideS point))
    joint jointDirection
    (rawReconstructionCore parameters (literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction))
    (rawReconstructionCore_directional _ _ _ _ genuine)
  have onLine :
      (fun scalar : ℝ => quotientEta parameters grade
        (rawFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction))) =
      (fun scalar : ℝ => quotientEta parameters grade
        (rawReconstructionCore parameters (fixedSliceMap parameters cellLength reference insideR seed insideS
          (joint + scalar • jointDirection)))) := by
    funext scalar
    rw [← rawFixedSliceCore_identity, realJointCoreToJoint_state_line]
    rfl
  rw [onLine]
  exact derivative

end Grad.RawForward
