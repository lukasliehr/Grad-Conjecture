import WM1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff

namespace Grad.Mollifier.WeakJets

theorem shiftedTest_contDiff (offset : Spatial) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (shiftedTest offset test) :=
  smoothness.comp (contDiff_id.add contDiff_const)

theorem shiftedTest_compactSupport (offset : Spatial) (test : Spatial → ℝ)
    (compactSupport : HasCompactSupport test) : HasCompactSupport (shiftedTest offset test) :=
  compactSupport.comp_homeomorph (Homeomorph.addRight offset)

theorem reflectedKernel_contDiff (offset : Spatial) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (reflectedKernel offset test) :=
  smoothness.comp (contDiff_const.sub contDiff_id)

theorem reflectedKernel_compactSupport (offset : Spatial) (test : Spatial → ℝ)
    (compactSupport : HasCompactSupport test) : HasCompactSupport (reflectedKernel offset test) := by
  have support : HasCompactSupport (fun source => test (offset + -source)) :=
    compactSupport.comp_homeomorph ((Homeomorph.neg Spatial).trans (Homeomorph.addLeft offset))
  change HasCompactSupport (fun source => test (offset - source))
  simpa only [sub_eq_add_neg] using support

theorem orderedTestDerivative_shifted (rank : ℕ) (word : Fin rank → Fin 2)
    (offset : Spatial) (test : Spatial → ℝ) (point : Spatial) :
    Grad.WeakTesting.orderedTestDerivative rank word (shiftedTest offset test) point =
      Grad.WeakTesting.orderedTestDerivative rank word test (point + offset) := by
  unfold Grad.WeakTesting.orderedTestDerivative shiftedTest
  rw [iteratedFDeriv_comp_add_right]

theorem orderedTestDerivative_reflected (rank : ℕ) (word : Fin rank → Fin 2)
    (offset : Spatial) (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) (point : Spatial) :
    Grad.WeakTesting.orderedTestDerivative rank word (reflectedKernel offset test) point =
      (-1 : ℝ) ^ rank * Grad.WeakTesting.orderedTestDerivative rank word test (offset - point) := by
  have shiftedSmooth : ContDiff ℝ (rank : ℕ) (shiftedTest offset test) :=
    (shiftedTest_contDiff offset test smoothness).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl rank)
  have reflected : reflectedKernel offset test =
      fun source => shiftedTest offset test ((-1 : ℝ) • source) := by
    funext source
    simp only [reflectedKernel, shiftedTest, neg_smul, one_smul, sub_eq_add_neg, add_comm]
  unfold Grad.WeakTesting.orderedTestDerivative
  rw [reflected, iteratedFDeriv_comp_const_smul (-1 : ℝ) shiftedSmooth]
  change ((-1 : ℝ) ^ rank • iteratedFDeriv ℝ rank (fun source => test (source + offset))
    ((-1 : ℝ) • point)) (fun position => spatialDirection (word position)) = _
  rw [iteratedFDeriv_comp_add_right]
  simp only [smul_apply, neg_smul, one_smul, smul_eq_mul]
  rw [show -point + offset = offset - point by abel]

theorem testGoal : TestGoal := by
  intro test smoothness compactSupport offset
  exact ⟨shiftedTest_contDiff offset test smoothness,
    shiftedTest_compactSupport offset test compactSupport,
    reflectedKernel_contDiff offset test smoothness,
    reflectedKernel_compactSupport offset test compactSupport,
    fun rank word point => orderedTestDerivative_shifted rank word offset test point,
    fun rank word point => orderedTestDerivative_reflected rank word offset test smoothness point⟩

end Grad.Mollifier.WeakJets
