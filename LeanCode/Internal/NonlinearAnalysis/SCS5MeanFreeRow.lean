import SCS4LowSourceGrade

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients

/-- Actual angular mean-free projection: only angular mode zero is removed;
every axial mode and every coefficient-created nonzero angular mode remains. -/
def meanFreeRowValue {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    DivisionRow dimension lower :=
  ⟨fun mode => if mode.1 = 0 then 0 else row mode, (lp.memℓp row).mono' (fun mode => by
    split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl])⟩

theorem meanFreeRowValue_norm_le {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    ‖meanFreeRowValue lower row‖ ≤ ‖row‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖if mode.1 = 0 then 0 else row mode‖ ≤ ‖row mode‖
  split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]

def meanFreeRowLinear {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →ₗ[ℂ] DivisionRow dimension lower where
  toFun := meanFreeRowValue lower
  map_add' first second := by
    apply lp.ext
    funext mode
    change (if mode.1 = 0 then 0 else first mode + second mode) =
      (if mode.1 = 0 then 0 else first mode) + (if mode.1 = 0 then 0 else second mode)
    split_ifs <;> simp
  map_smul' scalar row := by
    apply lp.ext
    funext mode
    change (if mode.1 = 0 then 0 else scalar • row mode) =
      scalar • (if mode.1 = 0 then 0 else row mode)
    split_ifs <;> simp

def meanFreeRow {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →L[ℂ] DivisionRow dimension lower :=
  LinearMap.mkContinuous (meanFreeRowLinear lower) 1 (fun row => by
    change ‖meanFreeRowValue lower row‖ ≤ 1 * ‖row‖
    simpa only [one_mul] using meanFreeRowValue_norm_le lower row)

theorem meanFreeRow_apply {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    meanFreeRow lower row mode = if mode.1 = 0 then 0 else row mode := rfl

theorem meanFreeRow_bound {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    ‖meanFreeRow lower row‖ ≤ ‖row‖ := meanFreeRowValue_norm_le lower row

theorem meanFreeRow_four_bound {dimension : ℕ} (lower : ℝ)
    (first second third fourth : DivisionRow dimension lower) :
    ‖meanFreeRow lower (first + second - third - fourth)‖ ≤
      ‖first‖ + ‖second‖ + ‖third‖ + ‖fourth‖ := by
  have h₁ : ‖first + second‖ ≤ ‖first‖ + ‖second‖ := norm_add_le first second
  have h₂ : ‖first + second - third‖ ≤ ‖first + second‖ + ‖third‖ :=
    norm_sub_le (first + second) third
  have h₃ : ‖first + second - third - fourth‖ ≤ ‖first + second - third‖ + ‖fourth‖ :=
    norm_sub_le (first + second - third) fourth
  have h₄ := meanFreeRow_bound lower (first + second - third - fourth)
  linarith only [h₁, h₂, h₃, h₄]

theorem meanFreeRow_square {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    meanFreeRow lower (meanFreeRow lower row) = meanFreeRow lower row := by
  apply lp.ext
  funext mode
  simp only [meanFreeRow_apply]
  split_ifs <;> rfl

end Grad.SourceCollarFullSource
