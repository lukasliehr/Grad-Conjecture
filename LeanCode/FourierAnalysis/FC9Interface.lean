import FC9Completion

noncomputable section

open Set

namespace Grad.CartesianState

/-- The exact FA-COR09 public boundary: the genuine norm completion, its
complex-linear isometric dense core embedding with the original M2 norm and
inner product, completeness, and the explicit real scalar restriction. -/
def CartesianCompletionGoal : Prop :=
  ∀ dimension parameters grade,
    DenseRange (aGradeEta parameters :
      GradeCore parameters dimension grade → AGrade parameters dimension grade) ∧
    Function.Injective (aGradeEta parameters :
      GradeCore parameters dimension grade → AGrade parameters dimension grade) ∧
    (∀ field : GradeCore parameters dimension grade,
      ‖aGradeEta parameters field‖ = ‖field‖ ∧
      ‖aGradeEta parameters field‖ = cartesianGradeSeminorm parameters field) ∧
    (∀ first second : GradeCore parameters dimension grade,
      inner ℂ (aGradeEta parameters first) (aGradeEta parameters second) =
        cartesianGradeInner parameters first second) ∧
    CompleteSpace (AGrade parameters dimension grade) ∧
    Nonempty (InnerProductSpace ℂ (AGrade parameters dimension grade)) ∧
    Nonempty (InnerProductSpace ℝ (AGrade parameters dimension grade)) ∧
    ∀ first second : AGrade parameters dimension grade,
      (Inner.rclikeToReal ℂ (AGrade parameters dimension grade)).inner
          first second =
        Complex.re (inner ℂ first second)

end Grad.CartesianState
