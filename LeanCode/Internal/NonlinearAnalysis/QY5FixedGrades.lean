import QY4FixedDerivatives

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ConstrainedGrades

theorem realJointLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealJointAmbient parameters reference insideR upper (large.trans ordered)) :
    ‖realJointLowering parameters reference insideR large ordered state‖ ≤ ‖state‖ := by
  rw [← realJointInclusion_norm parameters reference insideR lower large, realJointLowering_inclusion]
  exact (jointLowering_norm_le parameters ordered _).trans_eq
    (realJointInclusion_norm parameters reference insideR upper (large.trans ordered) state)

theorem realJointLowering_domain_iff {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealJointAmbient parameters reference insideR upper (large.trans ordered)) :
    realJointLowering parameters reference insideR large ordered state ∈
      realJointDomain parameters reference insideR lower large ↔
    state ∈ realJointDomain parameters reference insideR upper (large.trans ordered) := by
  change realJointInclusion parameters reference insideR lower large
    (realJointLowering parameters reference insideR large ordered state) ∈ jointDomain parameters lower ↔ _
  rw [realJointLowering_inclusion, jointLowering_domain_iff]
  rfl

theorem completedRealFixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealJointAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realJointDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS upper (large.trans ordered) state) =
      completedRealFixedSlice parameters cellLength reference insideR seed insideS lower large
        (realJointLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) state) := by
  apply Subtype.ext
  have loweredInside := (realJointLowering_domain_iff parameters reference insideR (realHighLarge lower)
    (Nat.add_le_add_right ordered 6) state).2 inside
  change zLowering parameters ordered (sourceInclusion parameters upper (large.trans ordered)
    (completedRealFixedSlice parameters cellLength reference insideR seed insideS upper (large.trans ordered) state)) =
    sourceInclusion parameters lower large (completedRealFixedSlice parameters cellLength reference insideR seed insideS
      lower large (realJointLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) state))
  rw [completedRealFixedSlice_inclusion parameters cellLength reference insideR seed insideS upper
    (large.trans ordered) state inside,
    completedRealFixedSlice_inclusion parameters cellLength reference insideR seed insideS lower large _ loweredInside]
  unfold completedRealFixedSliceAmbient
  rw [realJointLowering_inclusion]
  exact completedFixedSlice_gradeCompatibility parameters cellLength reference insideR seed insideS ordered _ inside

theorem completedRealFixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (order : ℕ)
    (state : RealJointAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realJointDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (directions : Fin order → RealJointAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered (iteratedFDeriv ℝ order
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS upper (large.trans ordered))
      state directions) =
    iteratedFDeriv ℝ order (completedRealFixedSlice parameters cellLength reference insideR seed insideS lower large)
      (realJointLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state)
      (fun position => realJointLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) (directions position)) := by
  apply Subtype.ext
  have loweredInside := (realJointLowering_domain_iff parameters reference insideR (realHighLarge lower)
    (Nat.add_le_add_right ordered 6) state).2 inside
  change zLowering parameters ordered (sourceInclusion parameters upper (large.trans ordered)
    (iteratedFDeriv ℝ order (completedRealFixedSlice parameters cellLength reference insideR seed insideS
      upper (large.trans ordered)) state directions)) =
    sourceInclusion parameters lower large (iteratedFDeriv ℝ order
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS lower large) _ _)
  rw [completedRealFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS
    upper (large.trans ordered) order state inside,
    completedRealFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS
      lower large order _ loweredInside,
    completedRealFixedSliceAmbient_derivative parameters cellLength reference insideR seed insideS upper order state inside,
    completedRealFixedSliceAmbient_derivative parameters cellLength reference insideR seed insideS lower order _ loweredInside]
  simp only [realJointLowering_inclusion]
  exact completedFixedSlice_derivative_gradeCompatibility parameters cellLength reference insideR seed insideS
    ordered order _ _ inside

end Grad.Q24Realization
