import AIW7ActualLowProductConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularCurrentLow

def originalLowToAJConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  1 + 2 * originalLowScaleConstant parameters length * (2 + length) + (1 + length⁻¹)

theorem originalLowToAJConstant_dominates (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) :
    2 * originalLowScaleConstant parameters length * (1 + length) ≤ originalLowToAJConstant parameters length ∧
    2 * originalLowScaleConstant parameters length ≤ originalLowToAJConstant parameters length ∧
    1 + length⁻¹ ≤ originalLowToAJConstant parameters length ∧ 1 ≤ originalLowToAJConstant parameters length := by
  have constant := originalLowScaleConstant_positive parameters length lengthPositive
  have inverse := inv_pos.mpr lengthPositive
  have product := mul_pos constant lengthPositive
  unfold originalLowToAJConstant
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem originalLow_muSlope_normalized (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    |lowMuSlope length radius cell| / lowMu length radius cell ^ 2 ≤ 1 := by
  have result := lowMuLogSlope_normalized_bound length radius cell positive
  rw [← lowMuSlope_div, abs_div, abs_of_pos (lowMu_pos length radius cell positive)] at result
  convert result using 1
  ring

/-- The three normalized physical coefficients before multiplication by r^7/4. -/
theorem originalLowToAJ_factors_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |originalLowRatio parameters lower length positive index radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ ∧
    |originalLowRatioSlope parameters lower length positive index radius| / cellFrequency index.2.val.2 ≤
      originalLowToAJConstant parameters length * lower⁻¹ ∧
    |originalLowRatio parameters lower length positive index radius| *
      lowMu length radius index.2.val.2 / cellFrequency index.2.val.2 ≤
      originalLowToAJConstant parameters length * lower⁻¹ := by
  have radiusPositive := positive.trans_le inside.1
  have inversePositive := inv_pos.mpr positive
  have inverseOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  have constants := originalLowToAJConstant_dominates parameters length lengthPositive
  have constantPositive : 0 < originalLowToAJConstant parameters length := zero_lt_one.trans_le constants.2.2.2
  rcases index with ⟨coordinate, mode⟩
  fin_cases coordinate
  · change |originalLowRatio parameters lower length positive (0, mode) radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ ∧
      |originalLowRatioSlope parameters lower length positive (0, mode) radius| / cellFrequency mode.val.2 ≤
        originalLowToAJConstant parameters length * lower⁻¹ ∧
      |originalLowRatio parameters lower length positive (0, mode) radius| * lowMu length radius mode.val.2 /
        cellFrequency mode.val.2 ≤ originalLowToAJConstant parameters length * lower⁻¹
    have aPositive := lowAmplitude_pos length parameters.gamma mode
    have sPositive := originalLowScale_positive parameters lower length positive lengthPositive mode
    have muPositive := lowMu_pos length radius mode.val.2 radiusPositive
    have lambdaPositive := cellFrequency_pos mode.val.2
    have sBound := originalLow_scale_over_amplitude parameters lower length positive bounded lengthPositive mode
    have lambdaBound := originalLow_lambda_over_mu length radius lengthPositive radiusPositive inside.2 mode.val.2
    have derivativeBound := originalLow_muSlope_normalized length radius mode.val.2 radiusPositive
    have ratio := originalLowRatio_first parameters lower length positive mode radius
    rw [originalLowSmoothMu_physical lower length positive mode.val.2 radius inside] at ratio
    have derivative := originalLowRatioSlope_first parameters lower length positive mode radius
    rw [originalLowSmoothMu_physical lower length positive mode.val.2 radius inside,
      originalLowSmoothMuSlope_physical lower length positive mode.val.2 radius inside] at derivative
    have ratioPositive := originalLowRatio_positive parameters lower length positive lengthPositive (0, mode) radius
    rw [abs_of_pos ratioPositive]
    constructor
    · rw [ratio]
      have compared := mul_le_mul sBound lambdaBound (div_nonneg lambdaPositive.le muPositive.le)
        (mul_nonneg (mul_nonneg (by norm_num) (originalLowScaleConstant_positive parameters length lengthPositive).le) inversePositive.le)
      have final := mul_le_mul_of_nonneg_right constants.1 inversePositive.le
      calc
        _ = (originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode) *
          (cellFrequency mode.val.2 / lowMu length radius mode.val.2) := by ring
        _ ≤ _ := compared
        _ ≤ _ := by nlinarith
    constructor
    · rw [derivative, abs_div, abs_mul, abs_neg, abs_mul,
        abs_of_pos (div_pos sPositive aPositive), abs_of_pos lambdaPositive,
        abs_of_pos (sq_pos_of_pos muPositive)]
      have equality :
          ((originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
            cellFrequency mode.val.2) * |lowMuSlope length radius mode.val.2| / lowMu length radius mode.val.2 ^ 2) /
              cellFrequency mode.val.2 =
          (originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode) *
            (|lowMuSlope length radius mode.val.2| / lowMu length radius mode.val.2 ^ 2) := by field_simp
      rw [equality]
      exact (mul_le_mul_of_nonneg_left derivativeBound (div_pos sPositive aPositive).le).trans
        (by simpa only [mul_one] using sBound.trans (mul_le_mul_of_nonneg_right constants.2.1 inversePositive.le))
    · rw [ratio]
      have equality :
          (originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
            cellFrequency mode.val.2 / lowMu length radius mode.val.2) * lowMu length radius mode.val.2 /
              cellFrequency mode.val.2 = originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode := by
        field_simp
      rw [equality]
      exact sBound.trans (mul_le_mul_of_nonneg_right constants.2.1 inversePositive.le)
  · change |originalLowRatio parameters lower length positive (1, mode) radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ ∧
      |originalLowRatioSlope parameters lower length positive (1, mode) radius| / cellFrequency mode.val.2 ≤
        originalLowToAJConstant parameters length * lower⁻¹ ∧
      |originalLowRatio parameters lower length positive (1, mode) radius| * lowMu length radius mode.val.2 /
        cellFrequency mode.val.2 ≤ originalLowToAJConstant parameters length * lower⁻¹
    rw [originalLowRatio_second, originalLowRatioSlope_second]
    norm_num only [ContinuousMap.one_apply, ContinuousMap.zero_apply, abs_one, abs_zero, zero_div, one_mul]
    constructor
    · nlinarith
    constructor
    · positivity
    · exact (originalLow_mu_over_lambda lower length radius positive lengthPositive bounded inside mode.val.2).trans
        (mul_le_mul_of_nonneg_right constants.2.2.1 inversePositive.le)

end Grad.AnnularOriginalLow
