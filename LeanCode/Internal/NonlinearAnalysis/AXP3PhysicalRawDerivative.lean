import AXP2PhysicalRaw

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RawForward
open Grad.NonlinearRange Grad.QuotientProjection Grad.Q24Realization Grad.RealFixedRanges

/-- Reconstructing the actual physical fixed chart derivative gives the
derivative of the original four raw rows in every original grade. -/
theorem physicalFixedSliceDerivative_rawDerivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    HasDerivAt
      (fun scalar : ℝ => quotientEta parameters grade
        (rawPhysicalFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction)))
      (quotientEta parameters grade (rawReconstructionCore parameters
        (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS 1
          (realJointCoreToJoint parameters reference insideR base)
          (fun _ => realJointCoreToJoint parameters reference insideR (0, direction))))) 0 := by
  let joint := realJointCoreToJoint parameters reference insideR base
  let jointDirection := realJointCoreToJoint parameters reference insideR (0, direction)
  have genuine : IsJointRowsDirectionalDerivative
      (physicalFixedSliceMap parameters cellLength reference insideR seed insideS) joint jointDirection
      (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS 1 joint (fun _ => jointDirection)) := by
    have step := composedDerivative_genuine (physicalFixedReferenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun order base directions admissible =>
        physicalFixedReferenceFamily_genuine reference insideR seed insideS order base directions admissible)
      cellLength 0 joint (fun _ => jointDirection) axis
    simp only [composedDerivative_zeroth, physicalFixedReferenceFamily_zero] at step
    convert step using 1 <;> rfl
  have derivative := coreRows_hasDerivAt parameters grade
    (fun point => rawReconstructionCore parameters
      (physicalFixedSliceMap parameters cellLength reference insideR seed insideS point))
    joint jointDirection
    (rawReconstructionCore parameters
      (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS 1 joint (fun _ => jointDirection)))
    (rawReconstructionCore_directional _ _ _ _ genuine)
  have onLine :
      (fun scalar : ℝ => quotientEta parameters grade
        (rawPhysicalFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction))) =
      (fun scalar : ℝ => quotientEta parameters grade
        (rawReconstructionCore parameters (physicalFixedSliceMap parameters cellLength reference insideR seed insideS
          (joint + scalar • jointDirection)))) := by
    funext scalar
    rw [← rawPhysicalFixedSliceCore_identity, realJointCoreToJoint_state_line]
    rfl
  rw [onLine]
  exact derivative

end Grad.PhysicalCoordinates
