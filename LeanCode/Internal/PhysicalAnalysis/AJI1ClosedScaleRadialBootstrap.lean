import AJH16OriginalSevenSlotSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore

theorem closedCollar_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (bounded : lower < 1) (order : ℕ) (field derivative : ℝ → E)
    (law : ∀ radius ∈ Icc lower 1, HasDerivWithinAt field (derivative radius) (Icc lower 1) radius)
    (smooth : ContDiffOn ℝ order derivative (Icc lower 1)) :
    ContDiffOn ℝ (order + 1 : ℕ) field (Icc lower 1) := by
  have unique : UniqueDiffOn ℝ (Icc lower 1) := uniqueDiffOn_Icc bounded
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin unique]
  refine ⟨fun radius inside => (law radius inside).differentiableWithinAt, by simp, ?_⟩
  exact (contDiffOn_congr (fun radius inside => (law radius inside).derivWithin (unique radius inside))).mpr smooth

/-- Radial induction quantifies over all tangential grades at every step.
The finite input loss is supplied from the same higher-grade field. -/
theorem closedScaleSystem_smooth
    (E : ℕ → Type*) [∀ grade, NormedAddCommGroup (E grade)]
    [∀ grade, NormedSpace ℂ (E grade)] [∀ grade, NormedSpace ℝ (E grade)]
    [∀ grade, IsScalarTower ℝ ℂ (E grade)]
    (lower : ℝ) (bounded : lower < 1) (loss : ℕ)
    (field source : ∀ grade, ℝ → E grade)
    (operator : ∀ grade, ℝ → E (grade + loss) →L[ℂ] E grade)
    (continuous : ∀ grade, ContinuousOn (field grade) (Icc lower 1))
    (sourceSmooth : ∀ grade, ContDiffOn ℝ ∞ (source grade) (Icc lower 1))
    (operatorSmooth : ∀ grade, ContDiffOn ℝ ∞ (operator grade) (Icc lower 1))
    (law : ∀ grade radius, radius ∈ Icc lower 1 → HasDerivWithinAt (field grade)
      ((operator grade radius) (field (grade + loss) radius) + source grade radius) (Icc lower 1) radius) :
    ∀ grade, ContDiffOn ℝ ∞ (field grade) (Icc lower 1) := by
  have orders (order : ℕ) : ∀ grade, ContDiffOn ℝ order (field grade) (Icc lower 1) := by
    induction order with
    | zero => exact fun grade => contDiffOn_zero.mpr (continuous grade)
    | succ order previous =>
      intro grade
      have action := ((ContinuousLinearMap.apply ℂ (E grade)).flip.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        ((contDiffOn_infty.mp (operatorSmooth grade)) order) (previous (grade + loss))
      exact closedCollar_succ lower bounded order (field grade) _ (law grade)
        (action.add ((contDiffOn_infty.mp (sourceSmooth grade)) order))
  exact fun grade => contDiffOn_infty.mpr (fun order => orders order grade)

end Grad.AnnularSmoothCore
