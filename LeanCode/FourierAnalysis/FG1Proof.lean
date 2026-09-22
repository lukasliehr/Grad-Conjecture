import FG1Interface

noncomputable section

namespace Grad.FourierGrade

theorem frequency_goal : FrequencyGoal := by
  intro mode
  exact ⟨frequencyVector_zero mode, frequencyVector_one mode, frequencyVector_two mode,
    frequencyWeight_sq mode, frequencyWeight_one_le mode⟩

theorem hilbert_goal : HilbertGoal := by
  intro dimension grade
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

theorem norm_goal : NormGoal := by
  intro Value _ _ grade field
  exact norm_sq_eq_weighted_tsum grade field

theorem inclusion_goal : InclusionGoal := by
  intro Value _ _ high middle low middleHigh lowMiddle
  exact ⟨inclusion_norm_le_one high middle middleHigh,
    inclusion_injective high middle middleHigh,
    inclusion_coefficient high middle middleHigh,
    inclusion_self high,
    inclusion_comp high middle low middleHigh lowMiddle⟩

theorem finite_density_goal : FiniteDensityGoal := by
  intro Value _ _ grade
  exact ⟨finiteCoefficientSpan_dense grade, coreToGrade_dense grade⟩

theorem core_goal : CoreGoal := by
  intro Value _ _ values grade source target ordered mode
  exact ⟨coreToGrade_coefficient grade values mode, coreToGrade_injective grade,
    inclusion_coreToGrade source target ordered values⟩

theorem block : BlockGoal :=
  ⟨frequency_goal, hilbert_goal, norm_goal, inclusion_goal, finite_density_goal, core_goal⟩

end Grad.FourierGrade
