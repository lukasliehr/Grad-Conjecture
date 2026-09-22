import Q24CompletedBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.Q24Realization

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints
open Grad.ConstrainedGrades

/-- The literal nonlinear realizations commute with the accepted
constant-one grade inclusions on their full original axis domain. -/
theorem completedFixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (state : JointAmbient parameters (upper + 6))
    (inside : state ∈ jointDomain parameters (upper + 6)) :
    zLowering parameters ordered
      (completedFixedSlice parameters cellLength reference insideR seed insideS upper state) =
    completedFixedSlice parameters cellLength reference insideR seed insideS lower
      (jointLowering parameters (Nat.add_le_add_right ordered 6) state) := by
  apply eq_on_open_of_dense (jointCoreEmbed parameters (upper + 6))
    (jointCoreEmbed_denseRange parameters (upper + 6)) (jointDomain parameters (upper + 6))
    (jointDomain_isOpen parameters (upper + 6))
    (fun value => zLowering parameters ordered
      (completedFixedSlice parameters cellLength reference insideR seed insideS upper value))
    (fun value => completedFixedSlice parameters cellLength reference insideR seed insideS lower
      (jointLowering parameters (Nat.add_le_add_right ordered 6) value))
  · exact (zLowering parameters ordered).continuous.comp_continuousOn
      (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS upper).continuousOn
  · exact (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS lower).continuousOn.comp
      (jointLowering parameters (Nat.add_le_add_right ordered 6)).continuous.continuousOn
      (fun value member => (jointLowering_domain_iff parameters (Nat.add_le_add_right ordered 6) value).2 member)
  · intro core member
    have axis := (jointDomain_core_iff parameters (upper + 6) core).1 member
    rw [completedFixedSlice_core parameters cellLength reference insideR seed insideS upper core axis,
      zLowering_core, jointLowering_core,
      completedFixedSlice_core parameters cellLength reference insideR seed insideS lower core axis]
  · exact inside

/-- All actual Fréchet derivatives commute on common grades, with every
independent direction lowered by the same canonical inclusion. -/
theorem completedFixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (order : ℕ)
    (state : JointAmbient parameters (upper + 6))
    (directions : Fin order → JointAmbient parameters (upper + 6))
    (inside : state ∈ jointDomain parameters (upper + 6)) :
    zLowering parameters ordered
      (iteratedFDeriv ℝ order
        (completedFixedSlice parameters cellLength reference insideR seed insideS upper) state directions) =
    iteratedFDeriv ℝ order
      (completedFixedSlice parameters cellLength reference insideR seed insideS lower)
      (jointLowering parameters (Nat.add_le_add_right ordered 6) state)
      (fun position => jointLowering parameters (Nat.add_le_add_right ordered 6) (directions position)) := by
  apply derivative_compatibility_of_dense_core (jointCoreEmbed parameters (upper + 6))
    (jointCoreEmbed_denseRange parameters (upper + 6))
    (jointLowering parameters (Nat.add_le_add_right ordered 6))
    ((zLowering parameters ordered).restrictScalars ℝ)
    (completedFixedSlice parameters cellLength reference insideR seed insideS upper)
    (completedFixedSlice parameters cellLength reference insideR seed insideS lower)
    (jointDomain parameters (upper + 6)) (jointDomain parameters (lower + 6))
    (jointDomain_isOpen parameters (upper + 6)) (jointDomain_isOpen parameters (lower + 6))
    (fun value member => (jointLowering_domain_iff parameters (Nat.add_le_add_right ordered 6) value).2 member)
    (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS upper)
    (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS lower) order
  · intro core tuple member
    have axis := (jointDomain_core_iff parameters (upper + 6) core).1 member
    change zLowering parameters ordered (iteratedFDeriv ℝ order
      (completedFixedSlice parameters cellLength reference insideR seed insideS upper)
      (jointCoreEmbed parameters (upper + 6) core)
      (fun position => jointCoreEmbed parameters (upper + 6) (tuple position))) = _
    rw [completedFixedSlice_derivative_core parameters cellLength reference insideR seed insideS upper order core axis,
      zLowering_core, jointLowering_core]
    simp only [jointLowering_core]
    exact (completedFixedSlice_derivative_core parameters cellLength reference insideR seed insideS lower order core axis tuple).symm
  · exact inside

end Grad.Q24Realization
