import SM4CutoffBounds

noncomputable section

namespace Grad.SmoothingFamily

open Grad.FourierGrade

def profileBound (order : ℕ) : ℝ := Classical.choose (scaleProfile_bounded order)

theorem profileBound_nonnegative (order : ℕ) : 0 ≤ profileBound order :=
  (Classical.choose_spec (scaleProfile_bounded order)).1

theorem scaleProfile_norm_le (order : ℕ) (scale : ℝ) :
    ‖scaleProfile order scale‖ ≤ profileBound order :=
  (Classical.choose_spec (scaleProfile_bounded order)).2 scale

def fourierScaleDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (order : ℕ) (scale : ℝ) : JCore Value →ₗ[ℂ] JCore Value :=
  boundedCoreMultiplier (fun mode => scaleMultiplier order (frequencyWeight mode) scale)
    (‖scale ^ (-(order : ℝ))‖ * profileBound order)
    (mul_nonneg (norm_nonneg _) (profileBound_nonnegative order)) (by
      intro mode
      rw [scaleMultiplier, norm_mul]
      exact mul_le_mul_of_nonneg_left (scaleProfile_norm_le order _) (norm_nonneg _))

theorem fourierScaleDerivative_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (order : ℕ) (scale : ℝ) (values : JCore Value) (mode : FourierMode) :
    (fourierScaleDerivative order scale values).1 mode =
      (scaleMultiplier order (frequencyWeight mode) scale : ℂ) • values.1 mode := rfl

theorem fourierScaleDerivative_zero {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) : fourierScaleDerivative (Value := Value) 0 scale = fourierSmoothing scale := by
  ext values mode
  change (scaleMultiplier 0 (frequencyWeight mode) scale : ℂ) • values.1 mode = _
  rw [scaleMultiplier_zero]
  rfl

theorem scalePower_identity (scale : ℝ) (positive : 0 < scale) (lower upper order : ℕ) :
    (scale ^ upper / scale ^ lower) * scale ^ (-(order : ℝ)) =
      scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) := by
  rw [← Real.rpow_natCast scale upper, ← Real.rpow_natCast scale lower,
    ← Real.rpow_sub positive, ← Real.rpow_add positive]
  congr 1

theorem derivative_weight_bound (frequency scale : ℝ) (frequencyPositive : 0 < frequency)
    (scalePositive : 0 < scale) (lower upper order : ℕ) (positiveOrder : 0 < order) :
    frequency ^ upper * ‖scaleMultiplier order frequency scale‖ ≤
      ((2 : ℝ) ^ upper * profileBound order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * frequency ^ lower := by
  by_cases zeroMultiplier : scaleMultiplier order frequency scale = 0
  · rw [zeroMultiplier, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (profileBound_nonnegative order))
        (Real.rpow_nonneg scalePositive.le _)) (pow_nonneg frequencyPositive.le _)
  obtain ⟨lowerFrequency, upperFrequency⟩ :=
    scaleMultiplier_support order positiveOrder frequency scale scalePositive zeroMultiplier
  have weightedProduct : frequency ^ upper * scale ^ lower ≤
      (2 * scale) ^ upper * frequency ^ lower :=
    mul_le_mul (pow_le_pow_left₀ frequencyPositive.le upperFrequency upper)
      (pow_le_pow_left₀ scalePositive.le lowerFrequency lower)
      (pow_nonneg scalePositive.le _) (pow_nonneg (by positivity) _)
  have weightBound : frequency ^ upper ≤
      (2 : ℝ) ^ upper * (scale ^ upper / scale ^ lower) * frequency ^ lower := by
    calc
      _ = (frequency ^ upper * scale ^ lower) / scale ^ lower := by
        rw [mul_div_cancel_right₀ _ (pow_ne_zero _ scalePositive.ne')]
      _ ≤ ((2 * scale) ^ upper * frequency ^ lower) / scale ^ lower :=
        div_le_div_of_nonneg_right weightedProduct (pow_nonneg scalePositive.le _)
      _ = _ := by rw [mul_pow]; ring
  have multiplierBound : ‖scaleMultiplier order frequency scale‖ ≤
      scale ^ (-(order : ℝ)) * profileBound order := by
    rw [scaleMultiplier, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg scalePositive.le _)]
    exact mul_le_mul_of_nonneg_left (scaleProfile_norm_le order _)
      (Real.rpow_nonneg scalePositive.le _)
  calc
    _ ≤ ((2 : ℝ) ^ upper * (scale ^ upper / scale ^ lower) * frequency ^ lower) *
        (scale ^ (-(order : ℝ)) * profileBound order) :=
      mul_le_mul weightBound multiplierBound (norm_nonneg _) (by positivity)
    _ = ((2 : ℝ) ^ upper * profileBound order) *
        ((scale ^ upper / scale ^ lower) * scale ^ (-(order : ℝ))) * frequency ^ lower := by ring
    _ = _ := by rw [scalePower_identity scale scalePositive]

/-- P20 in every pair of grades, including the case `upper < lower`. -/
theorem fourierScaleDerivative_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper order : ℕ) (positiveOrder : 0 < order)
    (values : JCore Value) :
    ‖coreToGrade upper (fourierScaleDerivative order scale values)‖ ≤
      ((2 : ℝ) ^ upper * profileBound order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * ‖coreToGrade lower values‖ := by
  apply core_norm_le_of_weighted_bound _ _ _ _ _
    (mul_nonneg (mul_nonneg (by positivity) (profileBound_nonnegative order))
      (Real.rpow_nonneg scalePositive.le _))
  intro mode
  rw [fourierScaleDerivative_apply, norm_smul, Complex.norm_real, ← mul_assoc]
  have scalarBound := derivative_weight_bound (frequencyWeight mode) scale (frequencyWeight_pos mode)
    scalePositive lower upper order positiveOrder
  exact (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg (values.1 mode))).trans_eq (by ring)

end Grad.SmoothingFamily
