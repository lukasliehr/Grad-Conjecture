import DE1Polynomial

noncomputable section

namespace Grad.DiskExtension.Seeley

theorem block : BlockGoal :=
  ⟨geometry_goal, finite_goal, finite_moment_goal, uniform_goal,
    limit_goal, summability_goal, moment_goal, polynomial_goal⟩

end Grad.DiskExtension.Seeley
