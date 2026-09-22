import AEE30OriginalLowInverseConsumer
import AEG3CompletedPhysicalSlots

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

theorem lowMode_abs_le_two (mode : LowAnnularMode) : |(mode.val.1 : ℝ)| ≤ 2 := by
  rcases mode.property with first | second
  · have equality : |(mode.val.1 : ℝ)| = 1 := by exact_mod_cast first
    rw [equality]
    norm_num
  · have equality : |(mode.val.1 : ℝ)| = 2 := by exact_mod_cast second
    rw [equality]

theorem lowAmplitude_upper (length gamma : ℝ) (mode : LowAnnularMode) :
    lowAmplitude length gamma mode ≤ lowBalanceConstant length gamma + 2 := by
  unfold lowAmplitude
  split_ifs
  · have root : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have balance : 1 ≤ lowBalanceConstant length gamma := le_max_left _ _
    have inverse : (Real.sqrt 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ root
    linarith
  · linarith

theorem lowAmplitude_inverse_bound (length gamma : ℝ) (mode : LowAnnularMode) :
    |(lowAmplitude length gamma mode)⁻¹| ≤ 2 := by
  rw [abs_of_pos (inv_pos.mpr (lowAmplitude_pos length gamma mode))]
  unfold lowAmplitude
  split_ifs
  · rw [inv_inv]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  · have balance : 1 ≤ lowBalanceConstant length gamma := le_max_left _ _
    exact (inv_le_one_of_one_le₀ balance).trans (by norm_num)

theorem lowMu_cell_abs (length radius : ℝ) (cell : ℤ) : |(cell : ℝ) / length| ≤ lowMu length radius cell := by
  have square := lowMu_sq length radius cell
  nlinarith [sq_nonneg radius⁻¹, lowMu_nonneg length radius cell, abs_nonneg ((cell : ℝ) / length), sq_abs ((cell : ℝ) / length)]

def lowCellMuRatio (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => ((cell : ℝ) / length) / lowMuCurve lower length positive cell radius,
    continuous_const.div (lowMuCurve lower length positive cell).continuous
      (fun radius => (lowMuCurve_pos lower length positive cell radius).ne')⟩

def lowRadiusMuRatio (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => (max lower radius)⁻¹ / lowMuCurve lower length positive cell radius,
    ((continuous_const.max continuous_id).inv₀ (fun _ => (positive.trans_le (le_max_left _ _)).ne')).div
      (lowMuCurve lower length positive cell).continuous
      (fun radius => (lowMuCurve_pos lower length positive cell radius).ne')⟩

theorem lowCellMuRatio_bound (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) (radius : ℝ) :
    |lowCellMuRatio lower length positive cell radius| ≤ 1 := by
  change |((cell : ℝ) / length) / lowMu length (max lower radius) cell| ≤ 1
  rw [abs_div, abs_of_pos (lowMu_pos length (max lower radius) cell (positive.trans_le (le_max_left _ _)))]
  exact (div_le_one (lowMuCurve_pos lower length positive cell radius)).mpr (lowMu_cell_abs _ _ _)

theorem lowRadiusMuRatio_bound (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) (radius : ℝ) :
    |lowRadiusMuRatio lower length positive cell radius| ≤ 1 := by
  have radiusPositive := positive.trans_le (le_max_left lower radius)
  change |(max lower radius)⁻¹ / lowMu length (max lower radius) cell| ≤ 1
  rw [abs_div, abs_of_pos (inv_pos.mpr radiusPositive), abs_of_pos (lowMu_pos length _ cell radiusPositive)]
  exact (div_le_one (lowMu_pos length _ cell radiusPositive)).mpr (lowMu_radial length _ cell radiusPositive)

theorem lowCellMuRatio_actual (lower length : ℝ) (positive : 0 < lower) (cell : ℤ)
    (radius : ℝ) (inside : lower ≤ radius) :
    lowCellMuRatio lower length positive cell radius = (cell : ℝ) / length / lowMu length radius cell := by
  change _ / lowMu length (max lower radius) cell = _
  rw [max_eq_right inside]

theorem lowRadiusMuRatio_actual (lower length : ℝ) (positive : 0 < lower) (cell : ℤ)
    (radius : ℝ) (inside : lower ≤ radius) :
    lowRadiusMuRatio lower length positive cell radius = radius⁻¹ / lowMu length radius cell := by
  change (max lower radius)⁻¹ / lowMu length (max lower radius) cell = _
  rw [max_eq_right inside]

end Grad.AnnularCurrentLow
