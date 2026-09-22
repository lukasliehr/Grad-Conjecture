import AIY6ExactStrengthenedAngularSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularLowEnergy
open Grad.AnnularCurrentLow Grad.AnnularCrossMaps

/-- The exact original low positive/negative half trace weights use nu,
whereas the BF4 incoming trace uses BE18's unchanged mu. -/
def lowIncomingNu (mode : LowAnnularMode) : ℝ :=
  Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2

theorem lowIncomingNu_pos (mode : LowAnnularMode) : 0 < lowIncomingNu mode :=
  zero_lt_one.trans_le (Grad.AnnularVariational.annularFrequency_one_le _ _)

theorem lowIncoming_mu_comparison (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    lowIncomingNu mode ≤ lowOuterFrequencyConstant length * lowMu length lower mode.val.2 ∧
    lowMu length lower mode.val.2 ≤
      lowOuterFrequencyConstant length * lower⁻¹ * lowIncomingNu mode := by
  have invOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  have innerSq := lowMu_sq length lower mode.val.2
  have outerSq := lowMu_sq length 1 mode.val.2
  have halfSq := lowMu_sq length (1 / 2) mode.val.2
  norm_num at outerSq halfSq
  have muMonotone : lowMu length 1 mode.val.2 ≤ lowMu length lower mode.val.2 := by
    nlinarith [lowMu_nonneg length lower mode.val.2, lowMu_nonneg length 1 mode.val.2]
  have scaling : lowMu length lower mode.val.2 ≤ lower⁻¹ * lowMu length (1 / 2) mode.val.2 := by
    have scaledCell := mul_nonneg (sq_nonneg ((mode.val.2 : ℝ) / length))
      (show 0 ≤ lower⁻¹ ^ 2 - 1 by nlinarith)
    nlinarith [lowMu_nonneg length lower mode.val.2, lowMu_nonneg length (1 / 2) mode.val.2,
      inv_pos.mpr positive, mul_nonneg (inv_nonneg.mpr positive.le) (lowMu_nonneg length (1 / 2) mode.val.2)]
  have constant := lowOuterFrequencyConstant_two_le length lengthPositive
  constructor
  · exact (lowFrequency_le_outerMu length lengthPositive mode).trans
      (mul_le_mul_of_nonneg_left muMonotone (by linarith))
  · exact scaling.trans ((mul_le_mul_of_nonneg_left
      (lowMu_half_le_frequency length lengthPositive mode) (inv_nonneg.mpr positive.le)).trans_eq (by dsimp [lowIncomingNu]; ring))

theorem lowIncoming_root_ratios (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    Real.sqrt (lowIncomingNu mode) / Real.sqrt (lowMu length lower mode.val.2) ≤
      lowOuterFrequencyConstant length ∧
    Real.sqrt (lowMu length lower mode.val.2) / Real.sqrt (lowIncomingNu mode) ≤
      lowOuterFrequencyConstant length * lower ^ (-(1 / 2 : ℝ)) := by
  have comparisons := lowIncoming_mu_comparison lower length positive bounded lengthPositive mode
  have nu := lowIncomingNu_pos mode
  have mu := lowMu_pos length lower mode.val.2 positive
  have constant := lowOuterFrequencyConstant_two_le length lengthPositive
  have constantSq : lowOuterFrequencyConstant length ≤ lowOuterFrequencyConstant length ^ 2 := by nlinarith
  have powerSq : (lower ^ (-(1 / 2 : ℝ))) ^ 2 = lower⁻¹ := by
    rw [pow_two, ← Real.rpow_add positive]
    norm_num [Real.rpow_neg_one]
  constructor
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr mu)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt nu.le, Real.sq_sqrt mu.le]
    exact comparisons.1.trans (mul_le_mul_of_nonneg_right constantSq mu.le)
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr nu)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt mu.le, Real.sq_sqrt nu.le, powerSq]
    exact comparisons.2.trans (by
      gcongr)

/-- Exact diagonal coefficient from original `(sqrt(nu) d,nu^-1/2 Rk)`
into BF4's `lower^-7/4 mu^-1/2 (a mu d,Rk)`.  The phase cancels. -/
def originalLowIncomingWeight (parameters : PhaseParameters) (lower length : ℝ)
    (index : LowAnnularIndex) : ℝ :=
  lower ^ (-(7 / 4 : ℝ)) *
    if index.1 = 0 then lowAmplitude length parameters.gamma index.2 *
      (Real.sqrt (lowMu length lower index.2.val.2) / Real.sqrt (lowIncomingNu index.2))
    else Real.sqrt (lowIncomingNu index.2) / Real.sqrt (lowMu length lower index.2.val.2)

def originalLowIncomingUnweight (parameters : PhaseParameters) (lower length : ℝ)
    (index : LowAnnularIndex) : ℝ :=
  lower ^ (7 / 4 : ℝ) *
    if index.1 = 0 then (lowAmplitude length parameters.gamma index.2)⁻¹ *
      (Real.sqrt (lowIncomingNu index.2) / Real.sqrt (lowMu length lower index.2.val.2))
    else Real.sqrt (lowMu length lower index.2.val.2) / Real.sqrt (lowIncomingNu index.2)

theorem originalLowIncomingWeight_pos (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    0 < originalLowIncomingWeight parameters lower length index := by
  unfold originalLowIncomingWeight
  have := lowAmplitude_pos length parameters.gamma index.2
  have := lowIncomingNu_pos index.2
  have := lowMu_pos length lower index.2.val.2 positive
  split_ifs <;> positivity

theorem originalLowIncomingUnweight_pos (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    0 < originalLowIncomingUnweight parameters lower length index := by
  unfold originalLowIncomingUnweight
  have := lowAmplitude_pos length parameters.gamma index.2
  have := lowIncomingNu_pos index.2
  have := lowMu_pos length lower index.2.val.2 positive
  split_ifs <;> positivity

theorem originalLowIncomingWeight_inverse (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    originalLowIncomingWeight parameters lower length index *
      originalLowIncomingUnweight parameters lower length index = 1 := by
  have nu := (Real.sqrt_pos.mpr (lowIncomingNu_pos index.2)).ne'
  have mu := (Real.sqrt_pos.mpr (lowMu_pos length lower index.2.val.2 positive)).ne'
  have amplitude := (lowAmplitude_pos length parameters.gamma index.2).ne'
  have powers : lower ^ (-(7 / 4 : ℝ)) * lower ^ (7 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add positive, neg_add_cancel, Real.rpow_zero]
  unfold originalLowIncomingWeight originalLowIncomingUnweight
  split_ifs <;> field_simp <;> nlinarith [powers]

def originalLowIncomingConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  (lowBalanceConstant length parameters.gamma + 2) * lowOuterFrequencyConstant length

theorem originalLowIncomingWeight_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (index : LowAnnularIndex) :
    |originalLowIncomingWeight parameters lower length index| ≤
      originalLowIncomingConstant parameters length * lower ^ (-9 / 4 : ℝ) := by
  rw [abs_of_pos (originalLowIncomingWeight_pos parameters lower length positive index)]
  have roots := lowIncoming_root_ratios lower length positive bounded lengthPositive index.2
  have constant := lowOuterFrequencyConstant_two_le length lengthPositive
  have balance : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  have powerPositive := (Real.rpow_pos_of_pos positive (-(7 / 4 : ℝ))).le
  have powers : lower ^ (-(7 / 4 : ℝ)) * lower ^ (-(1 / 2 : ℝ)) = lower ^ (-9 / 4 : ℝ) := by
    rw [← Real.rpow_add positive]
    norm_num
  have ordered : lower ^ (-(7 / 4 : ℝ)) ≤ lower ^ (-9 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge positive bounded (by norm_num)
  unfold originalLowIncomingWeight originalLowIncomingConstant
  split_ifs
  · have first := mul_le_mul (lowAmplitude_upper length parameters.gamma index.2) roots.2
      (by positivity) (by linarith : 0 ≤ lowBalanceConstant length parameters.gamma + 2)
    have result := mul_le_mul_of_nonneg_left first powerPositive
    apply result.trans_eq
    calc
      _ = (lowBalanceConstant length parameters.gamma + 2) * lowOuterFrequencyConstant length *
        (lower ^ (-(7 / 4 : ℝ)) * lower ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [powers]
  · have first := mul_le_mul_of_nonneg_left roots.1 powerPositive
    have second := mul_le_mul_of_nonneg_right ordered (by linarith : 0 ≤ lowOuterFrequencyConstant length)
    have extra := mul_nonneg (show 0 ≤ lowBalanceConstant length parameters.gamma + 1 by linarith)
      (mul_nonneg (show 0 ≤ lowOuterFrequencyConstant length by linarith) (Real.rpow_pos_of_pos positive (-9 / 4 : ℝ)).le)
    nlinarith only [first, second, extra]

theorem originalLowIncomingUnweight_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (index : LowAnnularIndex) :
    |originalLowIncomingUnweight parameters lower length index| ≤ 2 * lowOuterFrequencyConstant length := by
  rw [abs_of_pos (originalLowIncomingUnweight_pos parameters lower length positive index)]
  have roots := lowIncoming_root_ratios lower length positive bounded lengthPositive index.2
  have constant := lowOuterFrequencyConstant_two_le length lengthPositive
  have powerPositive := (Real.rpow_pos_of_pos positive (7 / 4 : ℝ)).le
  have powerLe : lower ^ (7 / 4 : ℝ) ≤ 1 := by
    exact Real.rpow_le_one positive.le bounded (by norm_num)
  have powers : lower ^ (7 / 4 : ℝ) * lower ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add positive]
    norm_num
    exact Real.rpow_le_one positive.le bounded (by norm_num)
  unfold originalLowIncomingUnweight
  split_ifs
  · have amplitude := lowAmplitude_inverse_bound length parameters.gamma index.2
    rw [abs_of_pos (inv_pos.mpr (lowAmplitude_pos length parameters.gamma index.2))] at amplitude
    have first := mul_le_mul amplitude roots.1 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    have second := mul_le_mul_of_nonneg_left first powerPositive
    nlinarith [mul_nonneg (show 0 ≤ 2 * lowOuterFrequencyConstant length by linarith) (show 0 ≤ 1 - lower ^ (7 / 4 : ℝ) by linarith)]
  · have first := mul_le_mul_of_nonneg_left roots.2 powerPositive
    have second := mul_le_mul_of_nonneg_left powers (show 0 ≤ lowOuterFrequencyConstant length by linarith)
    nlinarith only [first,second,constant]

end Grad.AnnularStrongData
