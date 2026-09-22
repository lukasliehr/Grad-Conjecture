import COR13Interface

namespace Grad.COR13Completion

theorem exactExtensionGoal : ExactExtensionGoal := by
  intro dimension grade parameters
  exact ⟨completedExtension_apply_eta parameters, completedRetraction_apply_core parameters,
    completedExtension_norm_le parameters, completedRetraction_norm_le parameters⟩

theorem completedRetractGoal : CompletedRetractGoal := by
  intro dimension grade parameters
  exact ⟨completedRetraction_extension parameters, realizationProjection_idempotent parameters,
    realizationProjection_norm_le parameters⟩

theorem closedRealizationGoal : ClosedRealizationGoal := by
  intro dimension grade parameters
  exact ⟨fixedRealization_closed parameters, fixedRealization_eq_range parameters,
    completedRealizationEquiv_apply parameters, completedRealizationEquiv_symm_apply parameters,
    completedRealizationEquiv_norm_le parameters, completedRealizationEquiv_symm_norm_le parameters⟩

theorem completedRetractClosedRealizationBlock : BlockGoal :=
  ⟨exactExtensionGoal, completedRetractGoal, closedRealizationGoal⟩

end Grad.COR13Completion
