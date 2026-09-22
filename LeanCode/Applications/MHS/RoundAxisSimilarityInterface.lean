import PhysicalSimilarity

noncomputable section

open Set

namespace Grad.MainAssembly.RoundAxisSimilarity

open Grad.MainTarget

/-- The exact `NG_R08` public contract, including the unequal-radius scale
formula and the independently proved vanishing of the translation. -/
def RoundAxisSimilarityGoal : Prop :=
  ∀ (sourceRadius targetRadius spatialScale : ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec),
    0 < sourceRadius → 0 < targetRadius → 0 < spatialScale →
    (fun point : Vec => spatialScale • orthogonal point + translation) ''
        roundAxis sourceRadius = roundAxis targetRadius →
    spatialScale * sourceRadius = targetRadius ∧ translation = 0

end Grad.MainAssembly.RoundAxisSimilarity
