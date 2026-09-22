import FC5Interface

noncomputable section

namespace Grad.CartesianState

theorem gradeNormDefiniteBlock : GradeNormDefiniteGoal := by
  intro dimension parameters grade
  refine ⟨cartesianGradeSeminorm_eq_zero_iff parameters,
    gradeCoreCoordinates_injective parameters,
    gradeCore_norm_eq_cartesianGradeSeminorm parameters,
    gradeCore_inner_eq_cartesianGradeInner parameters, ?_,
    gradeCoreCoordinateIsometry_injective parameters⟩
  rfl

end Grad.CartesianState
