import P0910GradeBound
import P0910Plateau

noncomputable section

namespace Grad.DiskExtension.Operator

theorem p0910_block_goal : BlockGoal := by
  refine ⟨plateau_goal, ordinaryExtensionRetraction, ?_⟩
  exact ⟨ordinaryExtensionRetraction_construction,
    ordinaryExtensionRetraction_smooth_boundary_support,
    ordinaryExtensionRetraction_linearity_real,
    ordinaryExtensionRetraction_cell_commutation,
    ordinaryExtensionRetraction_same_grade_bound⟩

end Grad.DiskExtension.Operator
