import BTInterface

noncomputable section

namespace Grad.BoundaryTrace

theorem weightedBoundaryTrace : BoundaryTraceGoal := by
  intro grade gradePositive
  refine ⟨traceCellConstant grade, traceCellConstant_nonnegative grade, ?_⟩
  intro dimension parameters field
  exact ⟨original_boundary_summable parameters grade gradePositive field,
    original_boundary_bound parameters grade gradePositive field⟩

theorem completedBoundaryTrace : CompletedBoundaryTraceGoal := by
  intro grade gradePositive
  refine ⟨Real.sqrt (traceCellConstant grade), Real.sqrt_nonneg _, ?_⟩
  intro dimension parameters
  exact ⟨completedTrace parameters grade gradePositive,
    completedTrace_norm_le parameters grade gradePositive,
    completedTrace_coefficient parameters grade gradePositive⟩

theorem weightedBoundaryTraceBlock : BlockGoal := ⟨weightedBoundaryTrace, completedBoundaryTrace⟩

end Grad.BoundaryTrace
