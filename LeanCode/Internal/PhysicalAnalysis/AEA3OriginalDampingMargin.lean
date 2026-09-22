import AEA2OriginalCircularMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

def lowDamping (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) : ℝ :=
  -annularPhaseSlope parameters cell radius

theorem lowDamping_formula (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) :
    lowDamping parameters radius cell = parameters.gamma *
      (radius * cellFrequency cell ^ 2 / Real.sqrt (1 + (radius * cellFrequency cell) ^ 2)) := by
  unfold lowDamping annularPhaseSlope
  have argument : 1 + cellFrequency cell ^ 2 * radius ^ 2 = 1 + (radius * cellFrequency cell) ^ 2 := by ring
  rw [argument]
  ring

theorem lowDamping_nonneg (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    0 ≤ lowDamping parameters radius cell := by
  rw [lowDamping_formula]
  exact mul_nonneg parameters.gamma_pos.le (div_nonneg (mul_nonneg positive.le (sq_nonneg _)) (Real.sqrt_nonneg _))

theorem frequency_damping_comparison (radius frequency : ℝ) (positive : 0 < radius) (frequencyPositive : 0 < frequency) :
    frequency ≤ Real.sqrt 2 * (radius * frequency ^ 2 / Real.sqrt (1 + (radius * frequency) ^ 2)) + radius⁻¹ := by
  have rootPositive : 0 < Real.sqrt (1 + (radius * frequency) ^ 2) := by positivity
  by_cases large : 1 ≤ radius * frequency
  · have rootBound : Real.sqrt (1 + (radius * frequency) ^ 2) ≤ Real.sqrt 2 * (radius * frequency) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (by positivity)]
      simp only [mul_pow]
      rw [Real.sq_sqrt (by norm_num)]
      nlinarith
    have comparison : frequency ≤ Real.sqrt 2 * (radius * frequency ^ 2 / Real.sqrt (1 + (radius * frequency) ^ 2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ rootPositive).mpr
      nlinarith [mul_le_mul_of_nonneg_left rootBound frequencyPositive.le]
    exact comparison.trans (le_add_of_nonneg_right (by positivity))
  · have short : frequency ≤ radius⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ positive).mpr
      simpa only [mul_comm] using (le_of_lt (lt_of_not_ge large))
    exact short.trans (le_add_of_nonneg_left (by positivity))

theorem lowDamping_frequency_comparison (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    cellFrequency cell ≤ Real.sqrt 2 * (lowDamping parameters radius cell / parameters.gamma) + radius⁻¹ := by
  rw [lowDamping_formula, mul_div_cancel_left₀ _ parameters.gamma_pos.ne']
  exact frequency_damping_comparison radius (cellFrequency cell) positive (cellFrequency_pos cell)

theorem lowMu_upper_lambda (length radius : ℝ) (cell : ℤ) (lengthPositive : 0 < length) (positive : 0 < radius) :
    lowMu length radius cell ≤ cellFrequency cell / length + radius⁻¹ := by
  have cellSquare : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  have muSquare := lowMu_sq length radius cell
  apply (sq_le_sq₀ (lowMu_nonneg _ _ _) (add_nonneg
    (div_nonneg (cellFrequency_pos cell).le lengthPositive.le) (inv_nonneg.mpr positive.le))).mp
  rw [add_sq, div_pow]
  rw [div_pow] at muSquare
  rw [cellSquare, add_div]
  nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg length),
    mul_nonneg (div_nonneg (cellFrequency_pos cell).le lengthPositive.le) (inv_nonneg.mpr positive.le)]

theorem lowEta_pos (length gamma : ℝ) (lengthPositive : 0 < length) (gammaPositive : 0 < gamma) :
    0 < lowEta length gamma := by
  unfold lowEta
  exact lt_min (by positivity) (by positivity)

/-- The original radius-independent margin in BE18, retaining eta_L exactly. -/
theorem lowWeighted_damping_margin (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (cell : ℤ) :
    lowEta length parameters.gamma * lowMu length radius cell ≤
      2 * lowDamping parameters radius cell + (1 / 2 : ℝ) * radius⁻¹ := by
  have frequency := lowDamping_frequency_comparison parameters radius cell positive
  have muBound := lowMu_upper_lambda length radius cell lengthPositive positive
  have etaPositive := lowEta_pos length parameters.gamma lengthPositive parameters.gamma_pos
  have first := min_le_left (Real.sqrt 2 * parameters.gamma * length) (length / (2 * (length + 1)))
  have second := min_le_right (Real.sqrt 2 * parameters.gamma * length) (length / (2 * (length + 1)))
  change lowEta length parameters.gamma ≤ _ at first second
  have firstCoefficient : lowEta length parameters.gamma * Real.sqrt 2 / (parameters.gamma * length) ≤ 2 := by
    have multiplied := mul_le_mul_of_nonneg_right first (Real.sqrt_nonneg 2)
    have sqrtSquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    apply (div_le_iff₀ (mul_pos parameters.gamma_pos lengthPositive)).mpr
    have product : Real.sqrt 2 * parameters.gamma * length * Real.sqrt 2 = 2 * (parameters.gamma * length) := by
      calc
        _ = Real.sqrt 2 ^ 2 * (parameters.gamma * length) := by ring
        _ = _ := by rw [sqrtSquare]
    rwa [product] at multiplied
  have secondCoefficient : lowEta length parameters.gamma * (1 / length + 1) ≤ 1 / 2 := by
    have relation := (le_div_iff₀ (by positivity : 0 < 2 * (length + 1))).mp second
    apply (le_of_mul_le_mul_left ?_ lengthPositive)
    field_simp
    nlinarith
  have expanded : lowEta length parameters.gamma * lowMu length radius cell ≤
      (lowEta length parameters.gamma * Real.sqrt 2 / (parameters.gamma * length)) * lowDamping parameters radius cell +
      (lowEta length parameters.gamma * (1 / length + 1)) * radius⁻¹ := by
    have upper := mul_le_mul_of_nonneg_left
      (muBound.trans (add_le_add_left (div_le_div_of_nonneg_right frequency lengthPositive.le) radius⁻¹)) etaPositive.le
    calc
      _ ≤ lowEta length parameters.gamma *
          ((Real.sqrt 2 * (lowDamping parameters radius cell / parameters.gamma) + radius⁻¹) / length + radius⁻¹) := upper
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  exact expanded.trans (add_le_add
    (mul_le_mul_of_nonneg_right firstCoefficient (lowDamping_nonneg parameters radius cell positive))
    (mul_le_mul_of_nonneg_right secondCoefficient (inv_nonneg.mpr positive.le)))

/-- BE2's exceptional coupling allocation retains its chosen c. -/
theorem lowBalance_small (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length) :
    4 / lowBalanceConstant length parameters.gamma ≤ lowEta length parameters.gamma / 4 := by
  have etaPositive := lowEta_pos length parameters.gamma lengthPositive parameters.gamma_pos
  have constantPositive : 0 < lowBalanceConstant length parameters.gamma := zero_lt_one.trans_le (le_max_left _ _)
  have bound : 16 / lowEta length parameters.gamma ≤ lowBalanceConstant length parameters.gamma :=
    (le_max_right _ _).trans (le_max_right _ _)
  have relation := (div_le_iff₀ etaPositive).mp bound
  apply (div_le_iff₀ constantPositive).mpr
  nlinarith

end Grad.AnnularLowReference
