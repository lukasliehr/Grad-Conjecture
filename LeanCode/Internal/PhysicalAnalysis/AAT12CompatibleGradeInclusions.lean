import AAT11ActualGradedInverse

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.CartesianState

section Inclusion
variable (lower length : ℝ) (positive : 0 < lower)
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)

def annularEnergyGradeInclusion : annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive
    (fun mode => annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode)
    1 (by norm_num)
    (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe)

def annularDataGradeInclusion : (AnnularForcing lower × AnnularBoundary) →L[ℂ]
    (AnnularForcing lower × AnnularBoundary) :=
  annularDataDiagonal lower
    (fun mode => annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode)
    1 (by norm_num)
    (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe)

theorem annularEnergyGradeInclusion_bound (field : annularEnergySpace lower length positive) :
    ‖annularEnergyGradeInclusion lower length positive angular cell inserted largerAngular largerCell largerInserted
      angularLe cellLe insertedLe field‖ ≤ ‖field‖ := by
  simpa only [annularEnergyGradeInclusion, one_mul] using
    annularEnergyDiagonal_bound lower length positive
      (fun mode => annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode)
      1 (by norm_num)
      (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) field

/-- Graded inclusion changes only normalized coordinates: the decoded
physical energy graph is exactly the same at every grade. -/
theorem annularEnergyGradeInclusion_decode (field : annularEnergySpace lower length positive) :
    annularEnergyDecode lower length positive angular cell inserted
      (annularEnergyGradeInclusion lower length positive angular cell inserted largerAngular largerCell largerInserted
        angularLe cellLe insertedLe field) =
      annularEnergyDecode lower length positive largerAngular largerCell largerInserted field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [annularEnergyDecode_apply, annularEnergyDecode_apply]
  change (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) •
    ((annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode : ℝ) : ℂ) • field.val mode = _
  rw [smul_smul, ← Complex.ofReal_mul]
  have coefficient : (annularGradeWeight angular cell inserted mode)⁻¹ *
      (annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode) =
        (annularGradeWeight largerAngular largerCell largerInserted mode)⁻¹ := by
    field_simp [(annularGradeWeight_pos angular cell inserted mode).ne',
      (annularGradeWeight_pos largerAngular largerCell largerInserted mode).ne']
  rw [coefficient]

theorem annularEnergyGradeInclusion_injective :
    Function.Injective (annularEnergyGradeInclusion lower length positive angular cell inserted
      largerAngular largerCell largerInserted angularLe cellLe insertedLe) := by
  intro first second equality
  apply annularEnergyDecode_injective lower length positive largerAngular largerCell largerInserted
  have decoded := congrArg (annularEnergyDecode lower length positive angular cell inserted) equality
  rw [annularEnergyGradeInclusion_decode, annularEnergyGradeInclusion_decode] at decoded
  exact decoded

include angularLe cellLe insertedLe in
theorem HasAnnularEnergyGrade.mono (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive largerAngular largerCell largerInserted field) :
    HasAnnularEnergyGrade lower length positive angular cell inserted field := by
  have decoded := annularEnergyGradeInclusion_decode lower length positive angular cell inserted
    largerAngular largerCell largerInserted angularLe cellLe insertedLe
    (annularWeightedEnergy lower length positive largerAngular largerCell largerInserted field grade)
  have identity := decoded.trans (annularEnergyDecode_weighted lower length positive largerAngular largerCell largerInserted field grade)
  exact (congrArg (HasAnnularEnergyGrade lower length positive angular cell inserted) identity).mp
    (annularEnergyDecode_hasGrade lower length positive angular cell inserted _)

theorem annularInverse_gradeInclusion (parameters : PhaseParameters) (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (data : AnnularForcing lower × AnnularBoundary) :
    annularEnergyGradeInclusion lower length positive angular cell inserted largerAngular largerCell largerInserted
      angularLe cellLe insertedLe
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) =
        annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
          (annularDataGradeInclusion lower angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data) :=
  annularVariationalInverse_diagonal parameters lower length positive collar lengthPositive widthHalf widthLength
    (fun mode => annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode)
    1 (by norm_num)
    (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) data

end Inclusion

end Grad.AnnularGrades
