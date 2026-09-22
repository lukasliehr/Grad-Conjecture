import FC2WeightedJet

noncomputable section

namespace Grad.CartesianState

theorem block : BlockGoal := by
  refine ⟨cellFrequency_one_le, cellFrequency_neg, cartesianPhase_neg,
    cartesianWeight_pos, cartesianWeight_one_le, ?_, ?_⟩
  · intro grade
    exact ⟨gradeMultiIndexEquiv grade⟩
  · intro dimension parameters cell field
    refine ⟨phaseWeightedJet parameters cell field, phaseWeightedJet_spec parameters cell field, ?_⟩
    intro candidate specification
    exact phaseWeightedJet_unique parameters cell field candidate specification

end Grad.CartesianState
