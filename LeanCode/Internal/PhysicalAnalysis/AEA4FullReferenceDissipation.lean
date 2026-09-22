import AEA3OriginalDampingMargin

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

theorem lowReferenceCross_bound (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) :
    |lowReferenceUpper length radius mode + lowReferenceLower length parameters.gamma radius mode| ≤
      (4 / lowBalanceConstant length parameters.gamma) * lowMu length radius mode.val.2 := by
  have constantPositive : 0 < lowBalanceConstant length parameters.gamma := zero_lt_one.trans_le (le_max_left _ _)
  have muPositive := lowMu_pos length radius mode.val.2 positive
  by_cases center : |mode.val.1| = 1
  · rw [lowReferenceUpper, lowReferenceLower, if_pos center, if_pos center, add_neg_cancel, abs_zero]
    positivity
  · rw [lowReferenceUpper, lowReferenceLower, if_neg center, if_neg center, zero_add,
      abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos (mul_pos constantPositive muPositive)]
    have radial := pow_le_pow_left₀ (inv_nonneg.mpr positive.le) (lowMu_radial length radius mode.val.2 positive) 2
    calc
      _ ≤ (4 * lowMu length radius mode.val.2 ^ 2) /
          (lowBalanceConstant length parameters.gamma * lowMu length radius mode.val.2) :=
        div_le_div_of_nonneg_right (by nlinarith) (mul_pos constantPositive muPositive).le
      _ = _ := by field_simp

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lowReferenceFirst (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second : E) : E :=
  (lowMuLogSlope length radius mode.val.2 - 2 / radius - lowDamping parameters radius mode.val.2) • first +
    lowReferenceUpper length radius mode • second

def lowReferenceSecond (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second : E) : E :=
  lowReferenceLower length parameters.gamma radius mode • first +
    (1 / radius - lowDamping parameters radius mode.val.2) • second

theorem lowReferenceFirst_matrix (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second : E) :
    lowReferenceFirst parameters length radius mode first second =
      lowReferenceMatrix parameters length radius mode 0 0 • first +
        lowReferenceMatrix parameters length radius mode 0 1 • second := by
  simp [lowReferenceFirst, lowReferenceMatrix, lowDamping]

theorem lowReferenceSecond_matrix (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second : E) :
    lowReferenceSecond parameters length radius mode first second =
      lowReferenceMatrix parameters length radius mode 1 0 • first +
        lowReferenceMatrix parameters length radius mode 1 1 • second := by
  simp [lowReferenceSecond, lowReferenceMatrix, lowDamping]

theorem lowPair_cross_bound (coefficient : ℝ) (first second : E) :
    2 * coefficient * inner ℝ first second ≤ |coefficient| * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  have innerBound := abs_real_inner_le_norm first second
  have young : 2 * |inner ℝ first second| ≤ ‖first‖ ^ 2 + ‖second‖ ^ 2 := by
    nlinarith [sq_nonneg (‖first‖ - ‖second‖)]
  calc
    _ ≤ 2 * |coefficient| * |inner ℝ first second| := by
      have bound := le_abs_self (coefficient * inner ℝ first second)
      rw [abs_mul] at bound
      linarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left young (abs_nonneg coefficient)]

/-- The derivative of mu^-1 contributes -mu'/mu exactly once. The center
cross terms cancel; the exceptional block retains its 4/c allocation. -/
theorem lowReference_weighted_form_bound (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (first second : E) :
    (-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius mode.val.2) * (‖first‖ ^ 2 + ‖second‖ ^ 2) +
      2 * inner ℝ first (lowReferenceFirst parameters length radius mode first second) +
      2 * inner ℝ second (lowReferenceSecond parameters length radius mode first second) ≤
    (-(2 * lowDamping parameters radius mode.val.2 + (1 / 2 : ℝ) / radius) +
      (4 / lowBalanceConstant length parameters.gamma) * lowMu length radius mode.val.2) *
        (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  have logNonpositive := lowMuLogSlope_nonpos length radius mode.val.2 positive
  have logBound := (abs_le.mp (lowMuLogSlope_abs_bound length radius mode.val.2 positive)).1
  have firstCoefficient : lowMuLogSlope length radius mode.val.2 - (15 / 2 : ℝ) / radius -
      2 * lowDamping parameters radius mode.val.2 ≤
      -(2 * lowDamping parameters radius mode.val.2 + (1 / 2 : ℝ) / radius) := by
    norm_num [div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr positive.le]
  have secondCoefficient : -lowMuLogSlope length radius mode.val.2 - (3 / 2 : ℝ) / radius -
      2 * lowDamping parameters radius mode.val.2 ≤
      -(2 * lowDamping parameters radius mode.val.2 + (1 / 2 : ℝ) / radius) := by
    norm_num [div_eq_mul_inv]
    linarith
  have firstBound := mul_le_mul_of_nonneg_right firstCoefficient (sq_nonneg ‖first‖)
  have secondBound := mul_le_mul_of_nonneg_right secondCoefficient (sq_nonneg ‖second‖)
  have cross := (lowPair_cross_bound
      (lowReferenceUpper length radius mode + lowReferenceLower length parameters.gamma radius mode) first second).trans
    (mul_le_mul_of_nonneg_right (lowReferenceCross_bound parameters length radius mode positive)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [lowReferenceFirst, lowReferenceSecond, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq] at ⊢
  have innerSwap : inner ℝ second first = inner ℝ first second := by apply real_inner_comm
  rw [innerSwap]
  linear_combination firstBound + secondBound + cross

/-- Original BE18 reference coercivity, on every low mode and every cell.
The remaining quarter of eta accommodates the actual current error later. -/
theorem lowReference_weighted_coercivity (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) (positive : 0 < radius) (first second : E) :
    (lowMu length radius mode.val.2)⁻¹ *
      ((-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius mode.val.2) * (‖first‖ ^ 2 + ‖second‖ ^ 2) +
        2 * inner ℝ first (lowReferenceFirst parameters length radius mode first second) +
        2 * inner ℝ second (lowReferenceSecond parameters length radius mode first second)) ≤
      -(3 * lowEta length parameters.gamma / 4) * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  have form := lowReference_weighted_form_bound parameters length radius mode positive first second
  have damping := lowWeighted_damping_margin parameters length radius lengthPositive positive mode.val.2
  have cross := mul_le_mul_of_nonneg_right (lowBalance_small parameters length lengthPositive)
    (lowMu_nonneg length radius mode.val.2)
  have coefficient : -(2 * lowDamping parameters radius mode.val.2 + (1 / 2 : ℝ) / radius) +
      (4 / lowBalanceConstant length parameters.gamma) * lowMu length radius mode.val.2 ≤
      -(3 * lowEta length parameters.gamma / 4) * lowMu length radius mode.val.2 := by
    rw [div_eq_mul_inv] at ⊢
    linarith
  have result := form.trans (mul_le_mul_of_nonneg_right coefficient (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have normalized := mul_le_mul_of_nonneg_left result (inv_nonneg.mpr (lowMu_nonneg length radius mode.val.2))
  have cancellation : (lowMu length radius mode.val.2)⁻¹ *
      (-(3 * lowEta length parameters.gamma / 4) * lowMu length radius mode.val.2 * (‖first‖ ^ 2 + ‖second‖ ^ 2)) =
      -(3 * lowEta length parameters.gamma / 4) * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
    field_simp [(lowMu_pos length radius mode.val.2 positive).ne']
  rwa [cancellation] at normalized

end Hilbert
end Grad.AnnularLowReference
