import MajorantProof

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds

/-- Submultiplicativity of the literal polynomial weight, without rescaling. -/
theorem polynomialWeight_add_le_mul (first second : ℤ) :
    cellPolynomialWeight (first + second) ≤
      cellPolynomialWeight first * cellPolynomialWeight second := by
  unfold cellPolynomialWeight
  push_cast
  have triangle := abs_add_le (first : ℝ) (second : ℝ)
  have positive := mul_nonneg (abs_nonneg (first : ℝ)) (abs_nonneg (second : ℝ))
  nlinarith

/-- The exact Q8 weight is submultiplicative at every fixed grade. -/
theorem weight_add_le_mul (parameters : PhaseParameters) (grade : ℕ)
    (first second : ℤ) :
    tameWeight parameters grade (first + second) ≤
      tameWeight parameters grade first * tameWeight parameters grade second := by
  have exponential := tameWeight_zero_add_le parameters first second
  simp only [tameWeight, pow_zero, mul_one] at exponential
  have polynomial := pow_le_pow_left₀ (cellPolynomialWeight_pos (first + second)).le
    (polynomialWeight_add_le_mul first second) grade
  rw [mul_pow] at polynomial
  unfold tameWeight
  calc _ ≤ (Real.exp (parameters.sigma0 * cellFrequency first) *
        Real.exp (parameters.sigma0 * cellFrequency second)) *
        (cellPolynomialWeight first ^ grade * cellPolynomialWeight second ^ grade) :=
      mul_le_mul exponential polynomial
        (pow_nonneg (cellPolynomialWeight_pos _).le _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by ring

/-- A nonnegative convolution estimate for the original Q8 weights. -/
theorem convolution_envelopeENN_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : ℤ → ℝ≥0∞) :
    (∑' cell, ENNReal.ofReal (tameWeight parameters grade cell) *
      ∑' shift, first shift * second (cell - shift)) ≤
      tameEnvelopeENN parameters grade first * tameEnvelopeENN parameters grade second := by
  calc _ = ∑' cell, ∑' shift,
        ENNReal.ofReal (tameWeight parameters grade cell) *
          (first shift * second (cell - shift)) := by
          simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' cell, ∑' shift,
        (ENNReal.ofReal (tameWeight parameters grade shift) * first shift) *
          (ENNReal.ofReal (tameWeight parameters grade (cell - shift)) *
            second (cell - shift)) := by
          apply ENNReal.tsum_le_tsum
          intro cell
          apply ENNReal.tsum_le_tsum
          intro shift
          have weightBound := weight_add_le_mul parameters grade shift (cell - shift)
          have sumLaw : shift + (cell - shift) = cell := by omega
          rw [sumLaw] at weightBound
          have lifted := ENNReal.ofReal_le_ofReal weightBound
          rw [ENNReal.ofReal_mul (tameWeight_pos _ _ _).le] at lifted
          calc _ ≤ (ENNReal.ofReal (tameWeight parameters grade shift) *
                ENNReal.ofReal (tameWeight parameters grade (cell - shift))) *
                (first shift * second (cell - shift)) := mul_le_mul' lifted le_rfl
            _ = _ := by ac_rfl
    _ = ∑' shift, ∑' cell,
        (ENNReal.ofReal (tameWeight parameters grade shift) * first shift) *
          (ENNReal.ofReal (tameWeight parameters grade (cell - shift)) *
            second (cell - shift)) := ENNReal.tsum_comm
    _ = ∑' shift, (ENNReal.ofReal (tameWeight parameters grade shift) * first shift) *
        tameEnvelopeENN parameters grade second := by
          apply tsum_congr
          intro shift
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact (Equiv.subRight shift).tsum_eq
            (fun cell => ENNReal.ofReal (tameWeight parameters grade cell) * second cell)
    _ = _ := by rw [ENNReal.tsum_mul_right]; rfl

/-- Submultiplicativity of the literal coefficient envelope, at every grade. -/
theorem envelope_mul_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : TameCoefficient parameters) :
    coefficientEnvelope grade (first * second) ≤
      coefficientEnvelope grade first * coefficientEnvelope grade second := by
  rw [← ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (coefficientEnvelope_nonneg _ _) (coefficientEnvelope_nonneg _ _))]
  rw [ENNReal.ofReal_mul (coefficientEnvelope_nonneg _ _), coefficientEnvelope,
    coefficientEnvelope, coefficientEnvelope,
    ← tameEnvelopeENN_normENN_eq (first * second).property grade,
    ← tameEnvelopeENN_normENN_eq first.property grade,
    ← tameEnvelopeENN_normENN_eq second.property grade]
  apply le_trans _ (convolution_envelopeENN_le parameters grade
    (tameNormENN first.val) (tameNormENN second.val))
  apply ENNReal.tsum_le_tsum
  intro cell
  apply mul_le_mul' le_rfl
  exact rawConvolution_normENN_le first.val second.val cell

end Grad.Q8FixedGrade
