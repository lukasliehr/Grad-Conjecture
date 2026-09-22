import RoundAxisSimilarity
import RoundAxisSimilarityInterface

noncomputable section

namespace Grad.MainAssembly.RoundAxisSimilarity

/-- Closed proof of the exact `NG_R08` public contract. -/
theorem roundAxisSimilarity : RoundAxisSimilarityGoal := by
  intro sourceRadius targetRadius spatialScale orthogonal translation
    sourcePositive targetPositive scalePositive axisEquality
  exact roundAxis_similarity_scale_translation sourceRadius targetRadius
    spatialScale orthogonal translation sourcePositive targetPositive
    scalePositive axisEquality

end Grad.MainAssembly.RoundAxisSimilarity
