import NewtonFiniteStage

noncomputable section

namespace Grad.NashMoser.Numeric

/-- A positive real-power threshold controls the inverse-power product,
including the zero coefficient case. -/
theorem inversePower_threshold {coefficient exponent time : ℝ}
    (coefficientNonnegative : 0 ≤ coefficient) (exponentPositive : 0 < exponent)
    (timePositive : 0 < time)
    (threshold : coefficient ^ (1 / exponent) ≤ time) :
    coefficient * time ^ (-exponent) ≤ 1 := by
  have coefficientBound : coefficient ≤ time ^ exponent := by
    have bound := Real.rpow_le_rpow
      (Real.rpow_nonneg coefficientNonnegative _) threshold exponentPositive.le
    rw [← Real.rpow_mul coefficientNonnegative,
      one_div_mul_cancel (ne_of_gt exponentPositive), Real.rpow_one] at bound
    exact bound
  calc
    coefficient * time ^ (-exponent) ≤ time ^ exponent * time ^ (-exponent) :=
      mul_le_mul_of_nonneg_right coefficientBound
        (Real.rpow_nonneg timePositive.le _)
    _ = 1 := by rw [← Real.rpow_add timePositive, add_neg_cancel, Real.rpow_zero]

/-- The explicit finite maximum from NM04. It never depends on a supremum
of high-grade constants or on a prospective solution. -/
def chosenInitial (radius highConstant quadratic smoothing : ℝ) (loss : ℕ) : ℝ :=
  max 4 (max ((4 * highConstant / radius) ^ (1 / (7 * (loss : ℝ) + 8)))
    (max ((2 * quadratic) ^ (1 / (2 * (loss : ℝ) + 4)))
      (Real.sqrt (2 * smoothing))))

theorem chosenInitial_large (radius highConstant quadratic smoothing : ℝ) (loss : ℕ) :
    4 ≤ chosenInitial radius highConstant quadratic smoothing loss := le_max_left _ _

theorem chosenInitial_guards
    (radius highConstant quadratic smoothing : ℝ) (loss : ℕ)
    (radiusPositive : 0 < radius) (highNonnegative : 0 ≤ highConstant)
    (quadraticNonnegative : 0 ≤ quadratic) (smoothingNonnegative : 0 ≤ smoothing) :
    let initial := chosenInitial radius highConstant quadratic smoothing loss
    4 ≤ initial ∧
      0 < initial ^ (-initialDecay loss) ∧
      2 * highConstant * initial ^ (-(initialDecay loss - loss)) ≤ radius / 2 ∧
      quadratic * initial ^ (-(2 * (loss : ℝ) + 4)) ≤ 1 / 2 ∧
      smoothing * initial ^ (-2 : ℝ) ≤ 1 / 2 := by
  dsimp only
  let initial := chosenInitial radius highConstant quadratic smoothing loss
  have large : 4 ≤ initial := chosenInitial_large _ _ _ _ _
  have positive : 0 < initial := by linarith
  have lowThreshold : (4 * highConstant / radius) ^ (1 / (7 * (loss : ℝ) + 8)) ≤
      initial := (le_max_left _ _).trans (le_max_right _ _)
  have quadraticThreshold : (2 * quadratic) ^ (1 / (2 * (loss : ℝ) + 4)) ≤
      initial := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have smoothingThreshold : Real.sqrt (2 * smoothing) ≤ initial :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have lowBound := inversePower_threshold
    (div_nonneg (mul_nonneg (by norm_num) highNonnegative) radiusPositive.le)
    (by positivity : 0 < 7 * (loss : ℝ) + 8) positive lowThreshold
  have quadraticBound := inversePower_threshold
    (mul_nonneg (by norm_num) quadraticNonnegative)
    (by positivity : 0 < 2 * (loss : ℝ) + 4) positive quadraticThreshold
  have smoothingBound := inversePower_threshold (coefficient := 2 * smoothing)
    (mul_nonneg (by norm_num) smoothingNonnegative)
    (by norm_num : (0 : ℝ) < 2) positive
    (by simpa only [Real.sqrt_eq_rpow] using smoothingThreshold)
  refine ⟨large, Real.rpow_pos_of_pos positive _, ?_, ?_, ?_⟩
  · have scaled := mul_le_mul_of_nonneg_right lowBound radiusPositive.le
    have identity : initialDecay (loss : ℝ) - loss = 7 * (loss : ℝ) + 8 := by
      unfold initialDecay
      ring
    rw [identity]
    have cancel : (4 * highConstant / radius *
        initial ^ (-(7 * (loss : ℝ) + 8))) * radius =
        4 * highConstant * initial ^ (-(7 * (loss : ℝ) + 8)) := by
      field_simp
    rw [cancel, one_mul] at scaled
    linarith
  · nlinarith
  · nlinarith

end Grad.NashMoser.Numeric
