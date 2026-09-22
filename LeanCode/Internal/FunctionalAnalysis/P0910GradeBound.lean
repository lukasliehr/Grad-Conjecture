import P0910ExteriorGrade

noncomputable section

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

theorem torusDerivativeGrade_periodizedExtension_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    torusDerivativeGrade grade (periodizedExtension field) ≤
      Real.sqrt (periodizedGradeEnergyFactor grade) *
        diskDerivativeGrade grade field := by
  rw [torusDerivativeGrade, diskDerivativeGrade]
  calc
    Real.sqrt (torusDerivativeEnergy grade (periodizedExtension field)) ≤
        Real.sqrt (periodizedGradeEnergyFactor grade *
          diskDerivativeEnergy grade field) :=
      Real.sqrt_le_sqrt
        (torusDerivativeEnergy_periodizedExtension_le field grade)
    _ = Real.sqrt (periodizedGradeEnergyFactor grade) *
        Real.sqrt (diskDerivativeEnergy grade field) := by
      rw [Real.sqrt_mul (periodizedGradeEnergyFactor_nonnegative grade)]

noncomputable def ordinaryExtensionRetractionGradeConstant (grade : ℕ) : ℝ :=
  max 16 (Real.sqrt (periodizedGradeEnergyFactor grade))

theorem ordinaryExtensionRetractionGradeConstant_nonnegative (grade : ℕ) :
    0 ≤ ordinaryExtensionRetractionGradeConstant grade := by
  unfold ordinaryExtensionRetractionGradeConstant
  exact le_max_of_le_left (by norm_num)

theorem ordinaryExtensionRetraction_extension_grade_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    torusDerivativeGrade grade
        (ordinaryExtensionRetraction.extension dimension field) ≤
      ordinaryExtensionRetractionGradeConstant grade *
        diskDerivativeGrade grade field := by
  change torusDerivativeGrade grade (periodizedExtension field) ≤ _
  exact (torusDerivativeGrade_periodizedExtension_le field grade).trans
    (mul_le_mul_of_nonneg_right
      (le_max_right 16 (Real.sqrt (periodizedGradeEnergyFactor grade)))
      (Real.sqrt_nonneg _))

theorem ordinaryExtensionRetraction_restriction_grade_le
    {dimension : ℕ} (field : TorusSmoothField dimension) (grade : ℕ) :
    diskDerivativeGrade grade
        (ordinaryExtensionRetraction.restriction dimension field) ≤
      ordinaryExtensionRetractionGradeConstant grade *
        torusDerivativeGrade grade field := by
  change diskDerivativeGrade grade (torusRestriction field) ≤ _
  exact (diskDerivativeGrade_restriction_le grade field).trans
    (mul_le_mul_of_nonneg_right
      (le_max_left 16 (Real.sqrt (periodizedGradeEnergyFactor grade)))
      (Real.sqrt_nonneg _))

theorem ordinaryExtensionRetraction_same_grade_bound :
    SameGradeBoundGoal ordinaryExtensionRetraction := by
  intro grade
  exact ⟨ordinaryExtensionRetractionGradeConstant grade,
    ordinaryExtensionRetractionGradeConstant_nonnegative grade,
    fun dimension field =>
      ordinaryExtensionRetraction_extension_grade_le field grade,
    fun dimension field =>
      ordinaryExtensionRetraction_restriction_grade_le field grade⟩

end Grad.DiskExtension.Operator
