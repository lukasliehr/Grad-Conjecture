import SM3FourierCore

noncomputable section

namespace Grad.SmoothingFamily

open Grad.FourierGrade

theorem smoothing_weight_bound (frequency scale : ℝ) (frequencyPositive : 0 < frequency)
    (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper) :
    frequency ^ upper * eta (frequency / scale) ≤
      (2 * scale) ^ (upper - lower) * frequency ^ lower := by
  by_cases cutoffZero : eta (frequency / scale) = 0
  · rw [cutoffZero, mul_zero]
    positivity
  have frequencyBound : frequency ≤ 2 * scale := by
    by_contra notBound
    exact cutoffZero (eta_zero _ ((le_div_iff₀ scalePositive).mpr (le_of_not_ge notBound)))
  calc
    _ ≤ frequency ^ upper := mul_le_of_le_one_right (pow_nonneg frequencyPositive.le _) (eta_range _).2
    _ = frequency ^ (upper - lower) * frequency ^ lower := by rw [← pow_add, Nat.sub_add_cancel ordered]
    _ ≤ (2 * scale) ^ (upper - lower) * frequency ^ lower :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ frequencyPositive.le frequencyBound _)
        (pow_nonneg frequencyPositive.le _)

theorem remainder_weight_bound (frequency scale : ℝ) (frequencyPositive : 0 < frequency)
    (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper) :
    frequency ^ lower * (1 - eta (frequency / scale)) ≤
      (scale ^ (upper - lower))⁻¹ * frequency ^ upper := by
  by_cases cutoffOne : eta (frequency / scale) = 1
  · rw [cutoffOne, sub_self, mul_zero]
    positivity
  have frequencyBound : scale ≤ frequency := by
    by_contra notBound
    exact cutoffOne (eta_one _ ((div_le_one scalePositive).mpr (le_of_not_ge notBound)))
  calc
    _ ≤ frequency ^ lower := mul_le_of_le_one_right (pow_nonneg frequencyPositive.le _)
      (by linarith [(eta_range (frequency / scale)).1])
    _ ≤ (scale ^ (upper - lower))⁻¹ * frequency ^ upper := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos scalePositive _)]
      calc
        _ ≤ frequency ^ lower * frequency ^ (upper - lower) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ scalePositive.le frequencyBound _)
            (pow_nonneg frequencyPositive.le _)
        _ = frequency ^ upper := by rw [← pow_add, Nat.add_sub_of_le ordered]

theorem rpow_grade_difference (scale : ℝ) (scaleNonnegative : 0 ≤ scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) :
    scale ^ ((lower : ℝ) - (upper : ℝ)) = (scale ^ (upper - lower))⁻¹ := by
  have exponent : (lower : ℝ) - (upper : ℝ) = -((upper - lower : ℕ) : ℝ) := by
    rw [Nat.cast_sub ordered]
    ring
  rw [exponent, Real.rpow_neg, Real.rpow_natCast]
  exact scaleNonnegative

/-- Exact first P19 estimate, including the literal factor `2T`. -/
theorem fourierSmoothing_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (values : JCore Value) :
    ‖coreToGrade upper (fourierSmoothing scale values)‖ ≤
      (2 * scale) ^ (upper - lower) * ‖coreToGrade lower values‖ := by
  apply core_norm_le_of_weighted_bound _ _ _ _ _ (by positivity)
  intro mode
  rw [fourierSmoothing_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (eta_range _).1, ← mul_assoc]
  have scalarBound := smoothing_weight_bound (frequencyWeight mode) scale (frequencyWeight_pos mode)
    scalePositive lower upper ordered
  exact (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg (values.1 mode))).trans_eq (by ring)

theorem fourierRemainder_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) (values : JCore Value) (mode : FourierMode) :
    (values - fourierSmoothing scale values).1 mode =
      ((1 - eta (frequencyWeight mode / scale) : ℝ) : ℂ) • values.1 mode := by
  change values.1 mode - (eta (frequencyWeight mode / scale) : ℂ) • values.1 mode = _
  rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]

/-- Exact second P19 estimate; the power is the signed real grade difference. -/
theorem fourierRemainder_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (values : JCore Value) :
    ‖coreToGrade lower (values - fourierSmoothing scale values)‖ ≤
      scale ^ ((lower : ℝ) - (upper : ℝ)) * ‖coreToGrade upper values‖ := by
  rw [rpow_grade_difference scale scalePositive.le lower upper ordered]
  apply core_norm_le_of_weighted_bound _ _ _ _ _ (by positivity)
  intro mode
  rw [fourierRemainder_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (eta_range _).2), ← mul_assoc]
  have scalarBound := remainder_weight_bound (frequencyWeight mode) scale (frequencyWeight_pos mode)
    scalePositive lower upper ordered
  exact (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg (values.1 mode))).trans_eq (by ring)

end Grad.SmoothingFamily
