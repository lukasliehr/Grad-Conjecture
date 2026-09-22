import AKU9FixedAxisPolynomialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.SourceCollarCoefficients
open Grad.NonlinearDivision Grad.GaugeCoefficients.Neumann.Regularity

/-- Original completed matrix coefficients, restricted to the actual axis.
The same grade-zero cells are used at all grades. -/
def axisFamilyOperator {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) :
    ℤ → ComplexEuclidean input →L[ℂ] ComplexEuclidean output :=
  fun cell => coefficientDerivative (family 0) cell (zeroDerivativeIndexAt 0) closedOrigin

theorem originalAxisEnvelope_weight (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    Real.exp (parameters.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade ≤
      (Real.exp parameters.sigma0 * 2 ^ grade) *
        (Real.exp (parameters.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade) := by
  have absolute : |(cell : ℝ)| ≤ cellFrequency cell := by
    change |(cell : ℝ)| ≤ Real.sqrt (1 + (cell : ℝ)^2)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have polynomial : cellPolynomialWeight cell ≤ 2 * cellFrequency cell := by
    rw [cellPolynomialWeight_formula]
    linarith [cellFrequency_one_le cell]
  have exponential : Real.exp (parameters.sigma0 * cellFrequency cell) ≤
      Real.exp parameters.sigma0 * Real.exp (parameters.sigma0 * |(cell : ℝ)|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have frequency := Grad.Constraints.Multipliers.frequency_le_polynomial cell
    rw [cellPolynomialWeight_formula] at frequency
    nlinarith [parameters.sigma0_pos]
  have power := pow_le_pow_left₀ (Grad.NonlinearQuotientBounds.cellPolynomialWeight_pos cell).le polynomial grade
  apply (mul_le_mul exponential power (pow_nonneg (Grad.NonlinearQuotientBounds.cellPolynomialWeight_pos cell).le _)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq
  rw [mul_pow]
  ring

theorem axisFamilyOperator_envelopeTerm_bound {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) (cell : ℤ) :
    Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family) cell ≤
      (Real.exp parameters.sigma0 * 2 ^ grade) *
        ‖weightedDerivative (family grade) cell (zeroDerivativeIndexAt grade)‖ := by
  have scale : coefficientScale 1 parameters.sigma0 parameters.gamma 1 grade cell (zeroDerivativeIndexAt grade) closedOrigin =
      Real.exp (parameters.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade := by
    simp [coefficientScale,originalEnvelope,scaledCellWeight,cellFrequency,Grad.CellWeights.cellWeight,
      closedOrigin,zeroDerivativeIndexAt,derivativeOrder]
  have literal := weighted_derivative_literal (L := 1) (sigma := parameters.sigma0)
    (gamma := parameters.gamma) (ell := 1) grade input output (family grade) cell
      (zeroDerivativeIndexAt grade) closedOrigin
  have normIdentity := congrArg norm literal
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg
    (coefficientScale_pos 1 parameters.sigma0 parameters.gamma 1 grade cell _ closedOrigin).le,scale] at normIdentity
  have same := coherent 0 grade (zeroDerivativeIndexAt 0) (zeroDerivativeIndexAt grade) rfl cell closedOrigin
  unfold Grad.Constraints.Multipliers.envelopeTerm axisFamilyOperator
  rw [same]
  calc _ ≤ ((Real.exp parameters.sigma0 * 2 ^ grade) *
      (Real.exp (parameters.sigma0 * |(cell : ℝ)|) * cellFrequency cell ^ grade)) *
        ‖coefficientDerivative (family grade) cell (zeroDerivativeIndexAt grade) closedOrigin‖ :=
    mul_le_mul_of_nonneg_right (originalAxisEnvelope_weight parameters grade cell) (norm_nonneg _)
  _ = (Real.exp parameters.sigma0 * 2 ^ grade) *
      ‖weightedDerivative (family grade) cell (zeroDerivativeIndexAt grade) closedOrigin‖ := by
    rw [mul_assoc,← normIdentity]
  _ ≤ _ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _)
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _))

theorem axisFamilyOperator_envelope_summable {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) :
    Summable (Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family)) :=
  Summable.of_nonneg_of_le (Grad.Constraints.Multipliers.envelopeTerm_nonnegative parameters grade _)
    (axisFamilyOperator_envelopeTerm_bound family coherent grade)
    ((coordinate_norm_summable (family grade).val (zeroDerivativeIndexAt grade)).mul_left _)

theorem axisFamilyOperator_envelope_bound {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) :
    Grad.Constraints.Multipliers.envelope parameters grade (axisFamilyOperator family) ≤
      (Real.exp parameters.sigma0 * 2 ^ grade) * ‖family grade‖ := by
  apply ((axisFamilyOperator_envelope_summable family coherent grade).tsum_le_tsum
    (axisFamilyOperator_envelopeTerm_bound family coherent grade)
    ((coordinate_norm_summable (family grade).val (zeroDerivativeIndexAt grade)).mul_left _)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le (family grade).val (zeroDerivativeIndexAt grade))
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _))

end Grad.FinitePhysicalJetLift
