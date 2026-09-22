import GaugeFourierConvolution

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.Constraints.Multipliers

theorem coefficientNorm_summable {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm phase 0 coefficients)) :
    Summable (fun cell => ‖coefficients cell‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ summable
  intro cell
  change ‖coefficients cell‖ ≤
    Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ 0 * ‖coefficients cell‖
  rw [pow_zero, mul_one]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg
    phase.sigma0_pos.le (cellFrequency_pos cell).le))

theorem originalValueNorm_summable {dimension : ℕ} (phase : PhaseParameters)
    (field : ACore phase dimension) (point : ClosedDisk) :
    Summable (fun cell => ‖(field.1 cell).value point‖) := by
  have majorant : Summable (fun cell => ‖(field.1 cell).value‖) := by
    simpa only [pow_zero, one_mul, closedDerivative_zero_order] using
      originalClosedDerivative_frequency_summable phase field emptyCartesianWord 0
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => ContinuousMap.norm_coe_le_norm _ point) majorant

theorem smoothMultiplier_value_hasSum {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (cell : ℤ) (point : ClosedDisk) :
    HasSum (fun shift : ℤ => coefficients shift ((field.1 (cell - shift)).value point))
      (((smoothMultiplier phase coefficients summable field).1 cell).value point) := by
  simpa only [closedDerivative_zero_order] using
    smoothMultiplier_derivative_hasSum phase coefficients summable field cell 0 emptyCartesianWord point

theorem smoothMultiplier_physical {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (point : ClosedDisk) (angle : ℝ) :
    originalPhysicalEvaluationLift phase
        (GradeCore.ofCoreLinear (grade := 0) (smoothMultiplier phase coefficients summable field)) point angle =
      (∑' cell : ℤ, cellExponential cell angle • coefficients cell)
        (originalPhysicalEvaluationLift phase (GradeCore.ofCoreLinear (grade := 0) field) point angle) := by
  rw [originalPhysicalEvaluationLift_eq_tsum, originalPhysicalEvaluationLift_eq_tsum]
  change (∑' cell : ℤ, cellExponential cell angle •
    ((smoothMultiplier phase coefficients summable field).1 cell).value point) = _
  have cellLaw (cell : ℤ) := (smoothMultiplier_value_hasSum phase coefficients summable field cell point).tsum_eq
  simp_rw [← cellLaw]
  exact operatorVectorConvolution_fourier coefficients (fun cell => (field.1 cell).value point)
    (coefficientNorm_summable phase coefficients (summable 0))
    (originalValueNorm_summable phase field point) angle

end Grad.Constraints.Gauges
