import PA3PhaseInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

/-- The actual FA-phase_algebra-phase theorem. -/
theorem actualPhaseSubadditive : PhaseSubadditiveGoal := by
  intro parameters radius lower upper n m
  exact radialPhase_subadditive parameters radius lower upper n m

/-- The actual FA-phase_algebra-equivalent theorem. -/
theorem actualPhaseEquivalent : PhaseEquivalentGoal := by
  intro parameters radius lower upper cell
  exact ⟨⟨phaseWeight_le_exp_radialPhase parameters radius lower upper cell,
    exp_radialPhase_le parameters radius lower upper cell⟩,
    cellFrequency_le_polynomial cell, polynomial_le_sqrt_two_mul cell⟩

end Grad.PhaseAlgebra
