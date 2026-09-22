import AIW5LiteralLowCoefficientIdentities

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularCurrentLow

theorem originalLow_cell_bounds (cell : ℤ) : 1 ≤ cellFrequency cell ∧ |(cell : ℝ)| ≤ cellFrequency cell := by
  have square : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  have positive := cellFrequency_pos cell
  constructor
  · nlinarith [sq_nonneg (cell : ℝ)]
  · nlinarith [sq_abs (cell : ℝ), abs_nonneg (cell : ℝ)]

theorem originalLow_mu_upper (length radius : ℝ) (lengthPositive : 0 < length)
    (positive : 0 < radius) (cell : ℤ) :
    lowMu length radius cell ≤ |(cell : ℝ)| / length + radius⁻¹ := by
  have square := lowMu_sq length radius cell
  have first : 0 ≤ |(cell : ℝ)| / length := by positivity
  have second : 0 ≤ radius⁻¹ := by positivity
  have absolute : (|(cell : ℝ)| / length) ^ 2 = ((cell : ℝ) / length) ^ 2 := by
    rw [div_pow, sq_abs, div_pow]
  nlinarith [lowMu_nonneg length radius cell, mul_nonneg first second]

theorem originalLow_mu_over_lambda (lower length radius : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    lowMu length radius cell / cellFrequency cell ≤ (1 + length⁻¹) * lower⁻¹ := by
  have cellBounds := originalLow_cell_bounds cell
  have radiusPositive := positive.trans_le inside.1
  have inverseRadius : radius⁻¹ ≤ lower⁻¹ := inv_anti₀ positive inside.1
  have inverseOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  have first : |(cell : ℝ)| / length ≤ cellFrequency cell * length⁻¹ := by
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right cellBounds.2 (inv_nonneg.mpr lengthPositive.le)
  have second : radius⁻¹ ≤ cellFrequency cell * lower⁻¹ :=
    inverseRadius.trans (by nlinarith [inv_pos.mpr positive])
  apply (div_le_iff₀ (cellFrequency_pos cell)).mpr
  have upper := originalLow_mu_upper length radius lengthPositive radiusPositive cell
  have multiplier : length⁻¹ + lower⁻¹ ≤ (1 + length⁻¹) * lower⁻¹ := by
    nlinarith [inv_pos.mpr lengthPositive]
  have scaled := mul_le_mul_of_nonneg_right multiplier (cellFrequency_pos cell).le
  nlinarith

theorem originalLow_lambda_over_mu (length radius : ℝ) (lengthPositive : 0 < length)
    (positive : 0 < radius) (bounded : radius ≤ 1) (cell : ℤ) :
    cellFrequency cell / lowMu length radius cell ≤ 1 + length :=
  (div_le_iff₀ (lowMu_pos length radius cell positive)).mpr
    (lowLambda_le_mu length radius cell lengthPositive positive bounded)

theorem originalLow_storage_bounds (lower radius : ℝ) (positive : 0 < lower)
    (inside : radius ∈ Icc lower 1) :
    0 < lowStorageInverse lower positive radius ∧ lowStorageInverse lower positive radius ≤ 1 ∧
    0 < lowStorageWeight lower positive radius ∧ lowStorageWeight lower positive radius ≤ lower ^ (-(7 / 4 : ℝ)) := by
  constructor
  · exact lowPowerCurve_pos lower (7 / 4 : ℝ) positive radius
  constructor
  · change (max lower radius) ^ (7 / 4 : ℝ) ≤ 1
    rw [max_eq_right inside.1]
    simpa using Real.rpow_le_rpow (positive.trans_le inside.1).le inside.2 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  constructor
  · exact lowPowerCurve_pos lower (-(7 / 4 : ℝ)) positive radius
  · change (max lower radius) ^ (-(7 / 4 : ℝ)) ≤ _
    rw [max_eq_right inside.1]
    exact Real.rpow_le_rpow_of_nonpos positive inside.1 (by norm_num)

def originalLowInverseBalanceConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  (lowBalanceConstant length parameters.gamma + 2) * (1 + Real.sqrt 3 * length)

theorem originalLowInverseBalanceConstant_positive (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) : 0 < originalLowInverseBalanceConstant parameters length := by
  have balance : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  unfold originalLowInverseBalanceConstant
  positivity

theorem originalLow_scale_over_amplitude (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode ≤
      2 * originalLowScaleConstant parameters length * lower⁻¹ := by
  have inverse := lowAmplitude_inverse_bound length parameters.gamma mode
  rw [abs_of_pos (inv_pos.mpr (lowAmplitude_pos length parameters.gamma mode))] at inverse
  have scale := originalLowScale_bound parameters lower length positive bounded lengthPositive mode
  have result := mul_le_mul scale inverse
    (inv_nonneg.mpr (lowAmplitude_pos length parameters.gamma mode).le)
    (mul_nonneg (originalLowScaleConstant_positive parameters length lengthPositive).le (inv_nonneg.mpr positive.le))
  simpa only [div_eq_mul_inv] using result.trans_eq (by ring)

theorem originalLow_amplitude_over_scale (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode ≤
      originalLowInverseBalanceConstant parameters length := by
  have amplitude := lowAmplitude_upper length parameters.gamma mode
  have scale := originalLowScale_inverse_bound parameters lower length positive lengthPositive mode
  have balance : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  exact mul_le_mul amplitude scale
    (inv_nonneg.mpr (originalLowScale_positive parameters lower length positive lengthPositive mode).le)
    (by linarith)

end Grad.AnnularOriginalLow
