import QY6MixedCodomain
import Q24RealMixedGrades

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

theorem completedRealMixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered
      (completedRealMixedSlice parameters cellLength reference insideR upper (large.trans ordered) state) =
      completedRealMixedSlice parameters cellLength reference insideR lower large
        (realMixedLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) state) := by
  apply Subtype.ext
  have loweredInside := (realMixedLowering_domain_iff parameters reference insideR (realHighLarge lower)
    (Nat.add_le_add_right ordered 6) state).2 inside
  change zLowering parameters ordered (sourceInclusion parameters upper (large.trans ordered)
    (completedRealMixedSlice parameters cellLength reference insideR upper (large.trans ordered) state)) =
    sourceInclusion parameters lower large (completedRealMixedSlice parameters cellLength reference insideR lower large
      (realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) state))
  rw [completedRealMixedSlice_inclusion parameters cellLength reference insideR upper (large.trans ordered) state inside,
    completedRealMixedSlice_inclusion parameters cellLength reference insideR lower large _ loweredInside]
  exact completedRealMixedSliceAmbient_gradeCompatibility parameters cellLength reference insideR ordered state inside

theorem completedRealMixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (order : ℕ)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered (iteratedFDeriv ℝ order
      (completedRealMixedSlice parameters cellLength reference insideR upper (large.trans ordered)) state directions) =
    iteratedFDeriv ℝ order (completedRealMixedSlice parameters cellLength reference insideR lower large)
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state)
      (fun position => realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (lower + 6) (realHighLarge lower)) := inferInstance
  exact derivative_compatibility_on_open
    (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))
    (sourceLowering parameters large ordered)
    (completedRealMixedSlice parameters cellLength reference insideR upper (large.trans ordered))
    (completedRealMixedSlice parameters cellLength reference insideR lower large)
    (realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain parameters reference insideR (lower + 6) (realHighLarge lower))
    (realMixedDomain_isOpen parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain_isOpen parameters reference insideR (lower + 6) (realHighLarge lower))
    (fun value member => (realMixedLowering_domain_iff parameters reference insideR
      (realHighLarge lower) (Nat.add_le_add_right ordered 6) value).2 member)
    (completedRealMixedSlice_contDiffOn parameters cellLength reference insideR upper (large.trans ordered))
    (completedRealMixedSlice_contDiffOn parameters cellLength reference insideR lower large)
    (completedRealMixedSlice_gradeCompatibility parameters cellLength reference insideR large ordered)
    order state inside directions

end Grad.Q24Realization
