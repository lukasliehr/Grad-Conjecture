import FC9Interface

noncomputable section

namespace Grad.CartesianState

theorem cartesianCompletionBlock : CartesianCompletionGoal := by
  intro dimension parameters grade
  refine ⟨aGradeEta_denseRange parameters, aGradeEta_injective parameters,
    ?_, aGradeEta_inner parameters,
    aGradeCompleteSpace parameters, ⟨aGradeComplexInnerProductSpace parameters⟩,
    ⟨aGradeRealInnerProductSpace parameters⟩,
    aGrade_real_inner_eq_re_complex parameters⟩
  intro field
  exact ⟨aGradeEta_norm parameters field,
    aGradeEta_norm_eq_cartesianGradeSeminorm parameters field⟩

end Grad.CartesianState
