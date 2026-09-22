import CircleIsometryClassification

noncomputable section

open Set

namespace Grad.MainAssembly.CircleIsometryClassification

open Grad.MainTarget

/-- Exact public contract for `NG_R07`. -/
def CircleIsometryClassificationGoal : Prop :=
  ∀ (radius : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec),
    0 < radius →
    (fun point : Vec => orthogonal point + translation) '' roundAxis radius =
      roundAxis radius →
    translation = 0 ∧
      ∃ tangentSign verticalSign angleShift : ℝ,
        (tangentSign = 1 ∨ tangentSign = -1) ∧
        (verticalSign = 1 ∨ verticalSign = -1) ∧
        (∀ angle,
          orthogonal (axisRadial angle) =
            axisRadial (tangentSign * angle + angleShift)) ∧
        (∀ angle,
          orthogonal (axisTangent angle) =
            tangentSign • axisTangent (tangentSign * angle + angleShift)) ∧
        orthogonal axisVertical = verticalSign • axisVertical ∧
        (coordinateMatrix orthogonal).det = tangentSign * verticalSign

end Grad.MainAssembly.CircleIsometryClassification
