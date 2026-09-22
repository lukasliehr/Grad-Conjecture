import AEA6ActualFiniteReferenceEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

theorem lowMu_cell (length radius : ℝ) (cell : ℤ) (lengthPositive : 0 < length) :
    |(cell : ℝ)| / length ≤ lowMu length radius cell := by
  calc
    _ = Real.sqrt (((cell : ℝ) / length) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos lengthPositive]
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem lowLambda_le_mu (length radius : ℝ) (cell : ℤ) (lengthPositive : 0 < length)
    (positive : 0 < radius) (bounded : radius ≤ 1) :
    cellFrequency cell ≤ (1 + length) * lowMu length radius cell := by
  have cellSquare : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  have first : cellFrequency cell ≤ 1 + |(cell : ℝ)| := by
    nlinarith [sq_abs (cell : ℝ), abs_nonneg (cell : ℝ), cellFrequency_pos cell]
  have second := (div_le_iff₀ lengthPositive).mp (lowMu_cell length radius cell lengthPositive)
  have one := lowMu_inner_one_le radius length positive bounded cell
  nlinarith

theorem lowDamping_upper (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) (_positive : 0 < radius) :
    lowDamping parameters radius cell ≤ parameters.gamma * cellFrequency cell := by
  have cellSquare : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  have square : lowDamping parameters radius cell ^ 2 ≤ parameters.gamma ^ 2 * cellFrequency cell ^ 2 := by
    simpa only [lowDamping, neg_sq, cellSquare] using annularPhaseSlope_sq_le parameters cell radius
  nlinarith [lowDamping_nonneg parameters radius cell _positive, parameters.gamma_pos,
    cellFrequency_pos cell, mul_pos parameters.gamma_pos (cellFrequency_pos cell)]

theorem lowDamping_normalized (parameters : PhaseParameters) (length radius : ℝ) (cell : ℤ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1) :
    lowDamping parameters radius cell ≤ (parameters.gamma * (1 + length)) * lowMu length radius cell := by
  exact (lowDamping_upper parameters radius cell positive).trans
    ((mul_le_mul_of_nonneg_left (lowLambda_le_mu length radius cell lengthPositive positive bounded)
      parameters.gamma_pos.le).trans_eq (by ring))

theorem lowReferenceUpper_bound (length radius : ℝ) (mode : LowAnnularMode) :
    |lowReferenceUpper length radius mode| ≤ 2 * lowMu length radius mode.val.2 := by
  unfold lowReferenceUpper
  split_ifs
  · rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (lowMu_nonneg _ _ _))]
    exact mul_le_mul_of_nonneg_right (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
      (lowMu_nonneg _ _ _)
  · rw [abs_zero]
    exact mul_nonneg (by norm_num) (lowMu_nonneg _ _ _)

theorem real_abs_sub_bound (first second : ℝ) : |first - second| ≤ |first| + |second| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le first second

theorem lowReferenceLower_bound (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) :
    |lowReferenceLower length parameters.gamma radius mode| ≤ 6 * lowMu length radius mode.val.2 := by
  have constantOne : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  have constantPositive : 0 < lowBalanceConstant length parameters.gamma := zero_lt_one.trans_le constantOne
  have ratio : 4 / lowBalanceConstant length parameters.gamma ≤ 4 := (div_le_iff₀ constantPositive).mpr (by linarith)
  have cross := (lowReferenceCross_bound parameters length radius mode positive).trans
    (mul_le_mul_of_nonneg_right ratio (lowMu_nonneg _ _ _))
  have upper := lowReferenceUpper_bound length radius mode
  have triangle := real_abs_sub_bound (lowReferenceUpper length radius mode + lowReferenceLower length parameters.gamma radius mode)
    (lowReferenceUpper length radius mode)
  have cancel : lowReferenceUpper length radius mode + lowReferenceLower length parameters.gamma radius mode -
      lowReferenceUpper length radius mode = lowReferenceLower length parameters.gamma radius mode := by ring
  rw [cancel] at triangle
  linarith

def lowReferenceCoefficientConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  7 + parameters.gamma * (1 + length)

theorem lowReferenceCoefficientConstant_pos (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length) :
    0 < lowReferenceCoefficientConstant parameters length := by
  unfold lowReferenceCoefficientConstant
  exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg parameters.gamma_pos.le (by linarith))

/-- Every actual matrix entry has a uniform mu-normalized bound, for all cells,
both low angular signs, and all original radii 0<r<=1. -/
theorem lowReferenceMatrix_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1)
    (mode : LowAnnularMode) (row column : Fin 2) :
    |lowReferenceMatrix parameters length radius mode row column| ≤
      lowReferenceCoefficientConstant parameters length * lowMu length radius mode.val.2 := by
  have muNonnegative := lowMu_nonneg length radius mode.val.2
  have phaseNonnegative := mul_nonneg parameters.gamma_pos.le (by linarith : 0 ≤ 1 + length)
  have dampingBound := lowDamping_normalized parameters length radius mode.val.2 lengthPositive positive bounded
  have dampingNonnegative := lowDamping_nonneg parameters radius mode.val.2 positive
  have radial := lowMu_radial length radius mode.val.2 positive
  have logBound := (lowMuLogSlope_abs_bound length radius mode.val.2 positive).trans radial
  fin_cases row <;> fin_cases column
  · change |lowMuLogSlope length radius mode.val.2 - 2 / radius + annularPhaseSlope parameters mode.val.2 radius| ≤ _
    have d : annularPhaseSlope parameters mode.val.2 radius = -lowDamping parameters radius mode.val.2 := by
      simp only [lowDamping, neg_neg]
    rw [d, ← sub_eq_add_neg]
    have triangle := (real_abs_sub_bound (lowMuLogSlope length radius mode.val.2 - 2 / radius)
      (lowDamping parameters radius mode.val.2)).trans
      (add_le_add_left (real_abs_sub_bound (lowMuLogSlope length radius mode.val.2) (2 / radius)) _)
    rw [abs_of_nonneg dampingNonnegative, abs_of_pos (div_pos (by norm_num) positive)] at triangle
    unfold lowReferenceCoefficientConstant
    norm_num [div_eq_mul_inv] at triangle ⊢
    nlinarith
  · change |lowReferenceUpper length radius mode| ≤ _
    unfold lowReferenceCoefficientConstant
    nlinarith [lowReferenceUpper_bound length radius mode, mul_nonneg phaseNonnegative muNonnegative]
  · change |lowReferenceLower length parameters.gamma radius mode| ≤ _
    unfold lowReferenceCoefficientConstant
    nlinarith [lowReferenceLower_bound parameters length radius mode positive, mul_nonneg phaseNonnegative muNonnegative]
  · change |1 / radius + annularPhaseSlope parameters mode.val.2 radius| ≤ _
    have d : annularPhaseSlope parameters mode.val.2 radius = -lowDamping parameters radius mode.val.2 := by
      simp only [lowDamping, neg_neg]
    rw [d, ← sub_eq_add_neg]
    have triangle := real_abs_sub_bound (1 / radius) (lowDamping parameters radius mode.val.2)
    rw [abs_of_pos (div_pos (by norm_num) positive), abs_of_nonneg dampingNonnegative] at triangle
    unfold lowReferenceCoefficientConstant
    norm_num [div_eq_mul_inv] at triangle ⊢
    nlinarith

end Grad.AnnularLowReference
