import FC4Interface

noncomputable section

namespace Grad.CartesianState

theorem gradeInnerBlock : GradeInnerBlockGoal := by
  intro dimension parameters grade
  refine ⟨⟨cartesianGradePreInnerCore parameters, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro first second
    rfl
  · exact cartesianGradeInner_self parameters
  · exact cartesianGradeSeminorm_triangle parameters
  · exact cartesianGradeSeminorm_smul parameters
  · exact cartesianGradeSeminorm_apply parameters
  · exact cartesianGradeSeminorm_sq parameters

end Grad.CartesianState

