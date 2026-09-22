import AAT14WeightedCutoffConvergence

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational

section Lp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)

theorem annularLpGradeInclusion_decode (field : lp (fun _ : HighAnnularMode => E) 2) :
    annularLpDecode angular cell inserted
      (realLpDiagonal
        (fun mode => annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode)
        1 (by norm_num)
        (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) field) =
      annularLpDecode largerAngular largerCell largerInserted field := by
  apply lp.ext
  funext mode
  change (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) •
    (((annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode : ℝ) : ℂ) • field mode) =
      (((annularGradeWeight largerAngular largerCell largerInserted mode)⁻¹ : ℝ) : ℂ) • field mode
  rw [smul_smul, ← Complex.ofReal_mul]
  congr 2
  field_simp [(annularGradeWeight_pos angular cell inserted mode).ne',
    (annularGradeWeight_pos largerAngular largerCell largerInserted mode).ne']

theorem annularLpWeighted_norm_sq (field : lp (fun _ : HighAnnularMode => E) 2)
    (grade : HasAnnularLpGrade angular cell inserted field) :
    ‖annularLpWeighted angular cell inserted field grade‖ ^ 2 =
      ∑' mode : HighAnnularMode, annularGradeWeight angular cell inserted mode ^ 2 * ‖field mode‖ ^ 2 := by
  rw [annularLpDecode_norm_sq angular cell inserted, annularLpDecode_weighted]

end Lp

section Data
variable (lower : ℝ)
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)

theorem annularDataGradeInclusion_decode (data : AnnularForcing lower × AnnularBoundary) :
    annularDataDecode lower angular cell inserted
      (annularDataGradeInclusion lower angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data) =
      annularDataDecode lower largerAngular largerCell largerInserted data := by
  apply Prod.ext
  · apply Prod.ext
    · exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data.1.1
    · apply Prod.ext
      · exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data.1.2.1
      · apply Prod.ext
        · exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data.1.2.2.1
        · exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data.1.2.2.2
  · exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe data.2

theorem annularDataDecode_injective : Function.Injective (annularDataDecode lower angular cell inserted) := by
  intro first second equality
  apply Prod.ext
  · apply Prod.ext
    · exact annularLpDecode_injective angular cell inserted (congrArg (fun data : AnnularForcing lower × AnnularBoundary => data.1.1) equality)
    · apply Prod.ext
      · exact annularLpDecode_injective angular cell inserted (congrArg (fun data : AnnularForcing lower × AnnularBoundary => data.1.2.1) equality)
      · apply Prod.ext
        · exact annularLpDecode_injective angular cell inserted (congrArg (fun data : AnnularForcing lower × AnnularBoundary => data.1.2.2.1) equality)
        · exact annularLpDecode_injective angular cell inserted (congrArg (fun data : AnnularForcing lower × AnnularBoundary => data.1.2.2.2) equality)
  · exact annularLpDecode_injective angular cell inserted (congrArg (fun data : AnnularForcing lower × AnnularBoundary => data.2) equality)

theorem annularDataGradeInclusion_injective :
    Function.Injective (annularDataGradeInclusion lower angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) := by
  intro first second equality
  apply annularDataDecode_injective lower largerAngular largerCell largerInserted
  have decoded := congrArg (annularDataDecode lower angular cell inserted) equality
  rw [annularDataGradeInclusion_decode, annularDataGradeInclusion_decode] at decoded
  exact decoded

end Data

end Grad.AnnularGrades
