import AIW11ExactInverseLowCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularCurrentLow

def originalLowFromAJConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  1 + originalLowInverseBalanceConstant parameters length * (2 + length⁻¹) + (1 + length)

theorem originalLowFromAJConstant_dominates (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) :
    originalLowInverseBalanceConstant parameters length * (1 + length⁻¹) ≤ originalLowFromAJConstant parameters length ∧
    originalLowInverseBalanceConstant parameters length ≤ originalLowFromAJConstant parameters length ∧
    1 + length ≤ originalLowFromAJConstant parameters length ∧ 1 ≤ originalLowFromAJConstant parameters length := by
  have constant := originalLowInverseBalanceConstant_positive parameters length lengthPositive
  have inverse := inv_pos.mpr lengthPositive
  have product := mul_pos constant inverse
  unfold originalLowFromAJConstant
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem originalLowFromAJ_factors_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |originalLowInverseRatio parameters lower length positive lengthPositive index radius| ≤
      originalLowFromAJConstant parameters length * lower⁻¹ ∧
    |originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius| /
        lowMu length radius index.2.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹ ∧
    cellFrequency index.2.val.2 * |originalLowInverseRatio parameters lower length positive lengthPositive index radius| /
        lowMu length radius index.2.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹ := by
  have radiusPositive := positive.trans_le inside.1
  have inversePositive := inv_pos.mpr positive
  have inverseOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  have constants := originalLowFromAJConstant_dominates parameters length lengthPositive
  have constantPositive : 0 < originalLowFromAJConstant parameters length := zero_lt_one.trans_le constants.2.2.2
  rcases index with ⟨coordinate, mode⟩
  fin_cases coordinate
  · change |originalLowInverseRatio parameters lower length positive lengthPositive (0, mode) radius| ≤
      originalLowFromAJConstant parameters length * lower⁻¹ ∧
      |originalLowInverseRatioSlope parameters lower length positive lengthPositive (0, mode) radius| /
        lowMu length radius mode.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹ ∧
      cellFrequency mode.val.2 * |originalLowInverseRatio parameters lower length positive lengthPositive (0, mode) radius| /
        lowMu length radius mode.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹
    have aPositive := lowAmplitude_pos length parameters.gamma mode
    have sPositive := originalLowScale_positive parameters lower length positive lengthPositive mode
    have muPositive := lowMu_pos length radius mode.val.2 radiusPositive
    have lambdaPositive := cellFrequency_pos mode.val.2
    have balance := originalLow_amplitude_over_scale parameters lower length positive lengthPositive mode
    have muBound := originalLow_mu_over_lambda lower length radius positive lengthPositive bounded inside mode.val.2
    have derivativeBound := originalLow_muSlope_lambda_bound lower length radius positive inside mode.val.2
    have ratio := originalLowInverseRatio_first parameters lower length positive lengthPositive mode radius
    rw [originalLowSmoothMu_physical lower length positive mode.val.2 radius inside] at ratio
    have derivative := originalLowInverseRatioSlope_first parameters lower length positive lengthPositive mode radius
    rw [originalLowSmoothMuSlope_physical lower length positive mode.val.2 radius inside] at derivative
    have ratioPositive : 0 < originalLowInverseRatio parameters lower length positive lengthPositive (0, mode) radius :=
      inv_pos.mpr (originalLowRatio_positive parameters lower length positive lengthPositive (0, mode) radius)
    rw [abs_of_pos ratioPositive]
    constructor
    · rw [ratio]
      have compared := mul_le_mul balance muBound (div_nonneg muPositive.le lambdaPositive.le)
        (originalLowInverseBalanceConstant_positive parameters length lengthPositive).le
      have final := mul_le_mul_of_nonneg_right constants.1 inversePositive.le
      calc
        _ = (lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode) *
          (lowMu length radius mode.val.2 / cellFrequency mode.val.2) := by ring
        _ ≤ _ := compared
        _ ≤ _ := by nlinarith
    constructor
    · rw [derivative, abs_div, abs_mul, abs_of_pos (div_pos aPositive sPositive), abs_of_pos lambdaPositive]
      have equality :
          (lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode *
            |lowMuSlope length radius mode.val.2| / cellFrequency mode.val.2) / lowMu length radius mode.val.2 =
          (lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode) *
            (|lowMuSlope length radius mode.val.2| / (lowMu length radius mode.val.2 * cellFrequency mode.val.2)) := by ring
      rw [equality]
      exact (mul_le_mul balance derivativeBound
        (div_nonneg (abs_nonneg _) (mul_pos muPositive lambdaPositive).le)
        (originalLowInverseBalanceConstant_positive parameters length lengthPositive).le).trans
        (mul_le_mul_of_nonneg_right constants.2.1 inversePositive.le)
    · rw [ratio]
      have equality : cellFrequency mode.val.2 *
          (lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode *
            lowMu length radius mode.val.2 / cellFrequency mode.val.2) / lowMu length radius mode.val.2 =
          lowAmplitude length parameters.gamma mode / originalLowScale parameters lower length mode := by field_simp
      rw [equality]
      exact balance.trans (constants.2.1.trans (by nlinarith))
  · change |originalLowInverseRatio parameters lower length positive lengthPositive (1, mode) radius| ≤
      originalLowFromAJConstant parameters length * lower⁻¹ ∧
      |originalLowInverseRatioSlope parameters lower length positive lengthPositive (1, mode) radius| /
        lowMu length radius mode.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹ ∧
      cellFrequency mode.val.2 * |originalLowInverseRatio parameters lower length positive lengthPositive (1, mode) radius| /
        lowMu length radius mode.val.2 ≤ originalLowFromAJConstant parameters length * lower⁻¹
    rw [originalLowInverseRatio_second, originalLowInverseRatioSlope_second]
    norm_num only [ContinuousMap.one_apply, ContinuousMap.zero_apply, abs_one, abs_zero, zero_div, mul_one]
    constructor
    · nlinarith
    constructor
    · positivity
    · exact (originalLow_lambda_over_mu length radius lengthPositive radiusPositive inside.2 mode.val.2).trans
        (constants.2.2.1.trans (by nlinarith))

/-- The requested BF6 power; the direct product actually gives ell^-11/4. -/
theorem originalLowFromAJ_storage_power (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    lower⁻¹ * lower ^ (-(7 / 4 : ℝ)) ≤ lower ^ (-(15 / 4 : ℝ)) := by
  have product : lower⁻¹ * lower ^ (-(7 / 4 : ℝ)) = lower ^ (-(11 / 4 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add positive]
    norm_num
  rw [product]
  exact Real.rpow_le_rpow_of_exponent_ge positive bounded (by norm_num)

end Grad.AnnularOriginalLow
