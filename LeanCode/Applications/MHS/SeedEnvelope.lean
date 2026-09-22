import SeedAlgebra

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Frame

theorem seedAdmissible (phase : PhaseParameters) : Admissible 1 phase.sigma0 phase.gamma 1 := by
  exact ⟨by norm_num, phase.gamma_pos, phase.gamma_lt_min, by norm_num, by norm_num⟩

def envelopeComparison (phase : PhaseParameters) (grade : ℕ) : ℝ :=
  Real.exp phase.sigma0 * 2 ^ grade

theorem envelopeComparison_nonnegative (phase : PhaseParameters) (grade : ℕ) :
    0 ≤ envelopeComparison phase grade := by unfold envelopeComparison; positivity

theorem polynomial_le_two_frequency (cell : ℤ) : cellPolynomialWeight cell ≤ 2 * cellFrequency cell := by
  have absBound : |(cell : ℝ)| ≤ cellFrequency cell := by
    change |(cell : ℝ)| ≤ Real.sqrt (1 + (cell : ℝ) ^ 2)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [cellPolynomialWeight_formula]
  linarith [cellFrequency_one_le cell]

theorem envelope_weight_comparison (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade ≤
      envelopeComparison phase grade * (Real.exp (phase.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade) := by
  have widthPositive : 0 ≤ phase.sigma0 :=
    (phase.gamma_pos.trans (parameters_gamma_lt_sigma0 phase)).le
  have exponential : Real.exp (phase.sigma0 * cellFrequency cell) ≤
      Real.exp phase.sigma0 * Real.exp (phase.sigma0 * |(cell : ℝ)|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have bound := mul_le_mul_of_nonneg_left (Multipliers.frequency_le_polynomial cell) widthPositive
    rw [cellPolynomialWeight_formula] at bound
    nlinarith
  have polynomial := pow_le_pow_left₀ (show 0 ≤ cellPolynomialWeight cell by
    rw [cellPolynomialWeight_formula]; positivity) (polynomial_le_two_frequency cell) grade
  calc
    _ ≤ (Real.exp phase.sigma0 * Real.exp (phase.sigma0 * |(cell : ℝ)|)) *
        (2 * cellFrequency cell) ^ grade :=
      mul_le_mul exponential polynomial
        (pow_nonneg (by rw [cellPolynomialWeight_formula]; positivity) _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by unfold envelopeComparison; rw [mul_pow]; ring

theorem coefficient_origin_norm_bound (phase : PhaseParameters) (grade : ℕ)
    (coefficient : Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2)
    (cells : ℤ → OperatorValue 2 2)
    (realization : ∀ cell, coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin = cells cell)
    (cell : ℤ) :
    Real.exp (phase.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade * ‖cells cell‖ ≤
      ‖weightedDerivative coefficient cell (zeroDerivativeIndexAt grade)‖ := by
  have literal := weighted_derivative_literal grade 2 2 coefficient cell (zeroDerivativeIndexAt grade) seedOrigin
  rw [realization] at literal
  have scale : coefficientScale 1 phase.sigma0 phase.gamma 1 grade cell (zeroDerivativeIndexAt grade) seedOrigin =
      Real.exp (phase.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade := by
    simp [coefficientScale, derivativeOrder_zeroDerivativeIndexAt, originalEnvelope, seedOrigin,
      scaledCellWeight, cellFrequency_formula]
  rw [scale] at literal
  have pointBound := ContinuousMap.norm_coe_le_norm (weightedDerivative coefficient cell (zeroDerivativeIndexAt grade)) seedOrigin
  rw [literal, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (cellFrequency_pos _).le _))] at pointBound
  exact pointBound

theorem coefficient_envelope_bound (phase : PhaseParameters) (grade : ℕ)
    (coefficient : Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2)
    (cells : ℤ → OperatorValue 2 2)
    (realization : ∀ cell, coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin = cells cell) :
    Summable (Multipliers.envelopeTerm phase grade cells) ∧
      Multipliers.envelope phase grade cells ≤ envelopeComparison phase grade * ‖coefficient‖ := by
  have pointwise (cell : ℤ) : Multipliers.envelopeTerm phase grade cells cell ≤
      envelopeComparison phase grade * ‖weightedDerivative coefficient cell (zeroDerivativeIndexAt grade)‖ := by
    unfold Multipliers.envelopeTerm
    calc
      _ ≤ (envelopeComparison phase grade *
          (Real.exp (phase.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade)) * ‖cells cell‖ :=
        mul_le_mul_of_nonneg_right (envelope_weight_comparison phase grade cell) (norm_nonneg _)
      _ = envelopeComparison phase grade *
          (Real.exp (phase.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade * ‖cells cell‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (coefficient_origin_norm_bound phase grade coefficient cells realization cell)
        (envelopeComparison_nonnegative phase grade)
  have majorant := (coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade)).mul_left
    (envelopeComparison phase grade)
  have summable : Summable (Multipliers.envelopeTerm phase grade cells) :=
    Summable.of_nonneg_of_le (fun cell => by
      unfold Multipliers.envelopeTerm
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (pow_nonneg (by rw [cellPolynomialWeight_formula]; positivity) _)) (norm_nonneg _)) pointwise majorant
  refine ⟨summable, ?_⟩
  apply (summable.tsum_le_tsum pointwise majorant).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val (zeroDerivativeIndexAt grade))
    (envelopeComparison_nonnegative phase grade)

end Grad.Constraints.Seed
