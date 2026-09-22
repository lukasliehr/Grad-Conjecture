import AAT15DataGradeCompatibility

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ActualBandCompletion

section Lp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem annularLpDecode_hasGrade (angular cell inserted : ℕ) (field : lp (fun _ : HighAnnularMode => E) 2) :
    HasAnnularLpGrade angular cell inserted (annularLpDecode angular cell inserted field) := by
  have summable : Memℓp (fun mode : HighAnnularMode => field mode) 2 := field.property
  unfold HasAnnularLpGrade
  simp only [annularLpDecode_normalization]
  exact summable

theorem annularLpDecode_cut (angular cell inserted : ℕ) (keep : Set HighAnnularMode)
    (field : lp (fun _ : HighAnnularMode => E) 2) :
    annularLpDecode angular cell inserted (lpCut keep field) = lpCut keep (annularLpDecode angular cell inserted field) := by
  classical
  apply lp.ext
  funext mode
  change (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) • lpCut keep field mode = _
  rw [lpCut_apply, lpCut_apply]
  by_cases member : mode ∈ keep <;> simp [member, annularLpDecode, realLpDiagonal_apply]

theorem annularLpDecode_mask (angular cell inserted : ℕ) (keep : Set HighAnnularMode)
    (field : lp (fun _ : HighAnnularMode => E) 2) :
    annularLpDecode angular cell inserted
      (realLpDiagonal (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) field) =
    realLpDiagonal (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)
      (annularLpDecode angular cell inserted field) := by
  rw [realLpDiagonal_mask, realLpDiagonal_mask]
  exact annularLpDecode_cut angular cell inserted keep field

end Lp

theorem annularDataDecode_hasGrade (lower : ℝ) (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary) :
    HasAnnularDataGrade lower angular cell inserted (annularDataDecode lower angular cell inserted data) :=
  ⟨annularLpDecode_hasGrade angular cell inserted data.1.1,
    annularLpDecode_hasGrade angular cell inserted data.1.2.1,
    annularLpDecode_hasGrade angular cell inserted data.1.2.2.1,
    annularLpDecode_hasGrade angular cell inserted data.1.2.2.2,
    annularLpDecode_hasGrade angular cell inserted data.2⟩

/-- The complete data model identifies exactly the prescribed weighted
physical source/boundary square sums. -/
theorem annularDataDecode_range_iff (lower : ℝ) (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary) :
    data ∈ LinearMap.range (annularDataDecode lower angular cell inserted).toLinearMap ↔
      HasAnnularDataGrade lower angular cell inserted data := by
  constructor
  · rintro ⟨normalized, rfl⟩
    exact annularDataDecode_hasGrade lower angular cell inserted normalized
  · intro grade
    exact ⟨annularWeightedData lower angular cell inserted data grade,
      annularDataDecode_weighted lower angular cell inserted data grade⟩

def annularDataCut (lower : ℝ) (keep : Set HighAnnularMode) :
    (AnnularForcing lower × AnnularBoundary) →L[ℂ] (AnnularForcing lower × AnnularBoundary) :=
  annularDataDiagonal lower (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)

theorem annularDataDecode_cut (lower : ℝ) (angular cell inserted : ℕ) (keep : Set HighAnnularMode)
    (data : AnnularForcing lower × AnnularBoundary) :
    annularDataDecode lower angular cell inserted (annularDataCut lower keep data) =
      annularDataCut lower keep (annularDataDecode lower angular cell inserted data) := by
  apply Prod.ext
  · apply Prod.ext
    · exact annularLpDecode_mask angular cell inserted keep data.1.1
    · apply Prod.ext
      · exact annularLpDecode_mask angular cell inserted keep data.1.2.1
      · apply Prod.ext
        · exact annularLpDecode_mask angular cell inserted keep data.1.2.2.1
        · exact annularLpDecode_mask angular cell inserted keep data.1.2.2.2
  · exact annularLpDecode_mask angular cell inserted keep data.2

theorem annularDataCut_tendsto (lower : ℝ) (data : AnnularForcing lower × AnnularBoundary) :
    Tendsto (fun support : Finset HighAnnularMode => annularDataCut lower (support : Set HighAnnularMode) data)
      atTop (𝓝 data) := by
  have convergence := ((lpCut_finset_tendsto data.1.1).prodMk_nhds
    ((lpCut_finset_tendsto data.1.2.1).prodMk_nhds
      ((lpCut_finset_tendsto data.1.2.2.1).prodMk_nhds (lpCut_finset_tendsto data.1.2.2.2)))).prodMk_nhds
        (lpCut_finset_tendsto data.2)
  have equality (support : Finset HighAnnularMode) :
      annularDataCut lower (support : Set HighAnnularMode) data =
        ((lpCut (support : Set HighAnnularMode) data.1.1,
          (lpCut (support : Set HighAnnularMode) data.1.2.1,
            (lpCut (support : Set HighAnnularMode) data.1.2.2.1, lpCut (support : Set HighAnnularMode) data.1.2.2.2))),
          lpCut (support : Set HighAnnularMode) data.2) := by
    apply Prod.ext
    · apply Prod.ext
      · exact realLpDiagonal_mask _ _
      · apply Prod.ext
        · exact realLpDiagonal_mask _ _
        · apply Prod.ext
          · exact realLpDiagonal_mask _ _
          · exact realLpDiagonal_mask _ _
    · exact realLpDiagonal_mask _ _
  exact convergence.congr' (Filter.Eventually.of_forall (fun support => (equality support).symm))

end Grad.AnnularGrades
