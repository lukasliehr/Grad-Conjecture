import FTP1315Interface

noncomputable section

namespace Grad.FourierGrade.P1315

theorem parseval_goal : ParsevalGoal := by
  intro dimension field
  exact ⟨euclidean_vector_fourier_series_L2 field,
    euclidean_torus_parseval field⟩

theorem weighted_grade_goal : WeightedGradeGoal := by
  intro dimension grade field
  exact norm_sq_eq_weighted_tsum grade field

theorem derivative_comparison_goal : DerivativeComparisonGoal := by
  intro dimension grade values
  exact ⟨derivativeCount_eq_choose grade,
    (actualDerivativeEnergy_comparison values).1,
    (actualDerivativeEnergy_comparison values).2,
    fun index => physicalMixedDerivative_physicalPoint index values⟩

theorem smooth_reconstruction_goal : SmoothReconstructionGoal := by
  intro dimension values
  exact ⟨hasSum_reconstructedTorus values,
    reconstructedPhysical_contDiff values,
    reconstructedPhysical_physicalPoint values,
    euclidean_reconstructedTorus_coefficient values⟩

theorem block : BlockGoal :=
  ⟨parseval_goal, weighted_grade_goal, derivative_comparison_goal,
    smooth_reconstruction_goal⟩

end Grad.FourierGrade.P1315
