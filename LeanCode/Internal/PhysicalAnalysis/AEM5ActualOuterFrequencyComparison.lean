import AEM4CompleteUniformLowOuterTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowOuterFrequencyConstant (length : ℝ) : ℝ := 3 + length + length⁻¹

theorem lowOuterFrequencyConstant_two_le (length : ℝ) (lengthPositive : 0 < length) :
    2 ≤ lowOuterFrequencyConstant length := by
  unfold lowOuterFrequencyConstant
  have inverse := inv_pos.mpr lengthPositive
  linarith

theorem lowMu_half_le_two_outer (length : ℝ) (cell : ℤ) :
    lowMu length (1 / 2) cell ≤ 2 * lowMu length 1 cell := by
  have half := lowMu_sq length (1 / 2) cell
  have outer := lowMu_sq length 1 cell
  norm_num at half outer
  nlinarith [lowMu_nonneg length (1 / 2) cell, lowMu_nonneg length 1 cell, sq_nonneg ((cell : ℝ) / length)]

theorem lowMu_half_le_frequency (length : ℝ) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    lowMu length (1 / 2) mode.val.2 ≤
      lowOuterFrequencyConstant length * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  have square := lowMu_sq length (1 / 2) mode.val.2
  norm_num at square
  have upper : lowMu length (1 / 2) mode.val.2 ≤ |(mode.val.2 : ℝ) / length| + 2 := by
    nlinarith [lowMu_nonneg length (1 / 2) mode.val.2, abs_nonneg ((mode.val.2 : ℝ) / length), sq_abs ((mode.val.2 : ℝ) / length)]
  rw [abs_div, abs_of_pos lengthPositive] at upper
  have frequencyOne := Grad.AnnularVariational.annularFrequency_one_le mode.val.1 mode.val.2
  have cell : |(mode.val.2 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ)]
  have scaled := mul_le_mul_of_nonneg_left cell (inv_nonneg.mpr lengthPositive.le)
  have rest : 2 ≤ (3 + length) * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    nlinarith
  unfold lowOuterFrequencyConstant
  change lowMu length (1 / 2) mode.val.2 ≤ |(mode.val.2 : ℝ)| * length⁻¹ + 2 at upper
  nlinarith

theorem lowFrequency_le_outerMu (length : ℝ) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ≤
      lowOuterFrequencyConstant length * lowMu length 1 mode.val.2 := by
  have one : 1 ≤ lowMu length 1 mode.val.2 := by simpa only [inv_one] using lowMu_radial length 1 mode.val.2 zero_lt_one
  have cell := lowMu_cell_abs length 1 mode.val.2
  rw [abs_div, abs_of_pos lengthPositive] at cell
  have cellBound := (div_le_iff₀ lengthPositive).mp cell
  have angular := lowMode_abs_le_two mode
  have inverse := inv_nonneg.mpr lengthPositive.le
  have extra := mul_nonneg inverse (lowMu_nonneg length 1 mode.val.2)
  unfold lowOuterFrequencyConstant Grad.AnnularVariational.annularFrequency
  nlinarith

end Grad.AnnularCrossMaps
