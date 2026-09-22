import COR16Interface

namespace Grad.CompatibleCompletion

theorem completedInclusionsBlock : CompletedInclusionGoal := by
  refine ⟨?_, ?_, ?_⟩
  · intro dimension lower upper parameters ordered
    exact ⟨completedInclusion_norm_le_one parameters ordered,
      completedInclusion_apply_eta parameters ordered,
      extension_inclusion_naturality parameters ordered,
      retraction_inclusion_naturality parameters ordered⟩
  · intro dimension grade parameters
    exact completedInclusion_self parameters
  · intro dimension high middle low parameters middleHigh lowMiddle
    exact completedInclusion_comp parameters middleHigh lowMiddle

theorem completedInjectivityBlock : CompletedInjectivityGoal := by
  intro dimension lower upper parameters ordered
  exact completedInclusion_injective parameters ordered

theorem smoothCompatibleLimitBlock : SmoothCompatibleLimitGoal := by
  intro dimension parameters
  exact ⟨compatibleToCore_toCompatible parameters, coreToCompatible_toCore parameters,
    coreCompatibleEquiv_component_norm parameters, coreCompatibleHomeomorph_apply parameters,
    originalGradedTopology_eq_induced parameters⟩

theorem compatibleCompletionBlock : BlockGoal :=
  ⟨completedInclusionsBlock, completedInjectivityBlock, smoothCompatibleLimitBlock⟩

end Grad.CompatibleCompletion
