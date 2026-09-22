import CircleIsometryClassificationProof

noncomputable section

open Set

namespace Grad.MainAssembly.CircleIsometryClassification.Consumer

open Grad.MainTarget
open Grad.MainAssembly.CircleIsometryClassification

/-- Immediate `NG_R05`/`NG_R17` consumer: in the moving normal frame the
radial coordinate is unchanged and only the vertical coordinate receives the
normal sign.  The planar orientation sign acts on the axis parameter and its
tangent, never on the radial normal coordinate. -/
theorem movingNormalFrame_action
    (radius : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (radiusPositive : 0 < radius)
    (axisEquality :
      (fun point : Vec => orthogonal point + translation) '' roundAxis radius =
        roundAxis radius) :
    translation = 0 ∧
      ∃ tangentSign verticalSign angleShift : ℝ,
        (tangentSign = 1 ∨ tangentSign = -1) ∧
        (verticalSign = 1 ∨ verticalSign = -1) ∧
        (∀ angle,
          orthogonal (axisTangent angle) =
            tangentSign • axisTangent (tangentSign * angle + angleShift)) ∧
        (∀ (angle radial vertical : ℝ),
          orthogonal
              (radial • axisRadial angle + vertical • axisVertical) =
            radial • axisRadial (tangentSign * angle + angleShift) +
              (verticalSign * vertical) • axisVertical) ∧
        (coordinateMatrix orthogonal).det = tangentSign * verticalSign := by
  rcases circleIsometryClassification radius orthogonal translation
      radiusPositive axisEquality with
    ⟨translationZero, tangentSign, verticalSign, angleShift,
      tangentSignValue, verticalSignValue, radialAction, tangentAction,
      verticalAction, determinant⟩
  refine ⟨translationZero, tangentSign, verticalSign, angleShift,
    tangentSignValue, verticalSignValue, tangentAction, ?_, determinant⟩
  intro angle radial vertical
  rw [map_add, map_smul, map_smul, radialAction, verticalAction]
  rw [smul_smul]
  rw [mul_comm vertical verticalSign]

end Grad.MainAssembly.CircleIsometryClassification.Consumer
