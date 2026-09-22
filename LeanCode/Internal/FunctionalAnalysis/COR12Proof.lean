import COR12Interface
import COR12Bounds

noncomputable section

namespace Grad.COR12Extension

theorem smoothWeightedExtensionRetractionBlock : BlockGoal := by
  refine ⟨?_, ?_, ?_⟩
  · intro dimension parameters
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  · intro grade
    refine ⟨sameGradeConstant grade, sameGradeConstant_nonnegative grade, ?_⟩
    intro dimension parameters
    exact ⟨fun field => weightedFourierExtension_norm_le parameters field grade,
      fun values => weightedFourierRetraction_norm_le parameters values grade⟩
  · intro dimension parameters field
    exact weightedFourierRetraction_extension parameters field

end Grad.COR12Extension
