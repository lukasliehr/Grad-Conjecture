import AIW10OriginalLowUnweightMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra

theorem originalLowInverseRatio_first (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) (radius : ℝ) :
    originalLowInverseRatio parameters lower length positive lengthPositive (0, mode) radius =
      lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode *
        originalLowSmoothMu lower length positive mode.val.2 radius / cellFrequency mode.val.2 := by
  change (originalLowRatio parameters lower length positive (0, mode) radius)⁻¹ = _
  rw [originalLowRatio_first]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem originalLowInverseRatio_second (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    originalLowInverseRatio parameters lower length positive lengthPositive (1, mode) = 1 := by
  apply ContinuousMap.ext
  intro radius
  change (originalLowRatio parameters lower length positive (1, mode) radius)⁻¹ = 1
  rw [originalLowRatio_second]
  exact inv_one

theorem originalLowInverseRatioSlope_formula (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius =
      -(originalLowInverseRatio parameters lower length positive lengthPositive index radius *
        originalLowRatioSlope parameters lower length positive index radius) /
          originalLowRatio parameters lower length positive index radius := by
  apply (eq_div_iff (originalLowRatio_positive parameters lower length positive lengthPositive index radius).ne').mpr
  linarith only [originalLowRatio_slope_cancel parameters lower length positive lengthPositive index radius]

theorem originalLowInverseRatioSlope_first (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) (radius : ℝ) :
    originalLowInverseRatioSlope parameters lower length positive lengthPositive (0, mode) radius =
      lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode *
        originalLowSmoothMuSlope lower length positive mode.val.2 radius / cellFrequency mode.val.2 := by
  rw [originalLowInverseRatioSlope_formula, originalLowInverseRatio_first, originalLowRatioSlope_first, originalLowRatio_first]
  have amplitude := (lowAmplitude_pos length parameters.gamma mode).ne'
  have scale := (originalLowScale_positive parameters lower length positive lengthPositive mode).ne'
  have mu := (originalLowSmoothMu_pos lower length positive mode.val.2 radius).ne'
  have frequency := (cellFrequency_pos mode.val.2).ne'
  field_simp

theorem originalLowInverseRatioSlope_second (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    originalLowInverseRatioSlope parameters lower length positive lengthPositive (1, mode) = 0 := by
  apply ContinuousMap.ext
  intro radius
  rw [originalLowInverseRatioSlope_formula, originalLowRatioSlope_second]
  simp

theorem originalLow_muSlope_lambda_bound (lower length radius : ℝ) (positive : 0 < lower)
    (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    |lowMuSlope length radius cell| / (lowMu length radius cell * cellFrequency cell) ≤ lower⁻¹ := by
  have radiusPositive := positive.trans_le inside.1
  have muPositive := lowMu_pos length radius cell radiusPositive
  have first := lowMuLogSlope_abs_bound length radius cell radiusPositive
  rw [← lowMuSlope_div, abs_div, abs_of_pos muPositive] at first
  have frequency := (originalLow_cell_bounds cell).1
  have second : (|lowMuSlope length radius cell| / lowMu length radius cell) / cellFrequency cell ≤ radius⁻¹ := by
    apply (div_le_iff₀ (cellFrequency_pos cell)).mpr
    exact first.trans (by nlinarith [inv_pos.mpr radiusPositive])
  have adjusted : |lowMuSlope length radius cell| / (lowMu length radius cell * cellFrequency cell) =
      (|lowMuSlope length radius cell| / lowMu length radius cell) / cellFrequency cell := by ring
  rw [adjusted]
  exact second.trans (inv_anti₀ positive inside.1)

end Grad.AnnularOriginalLow
