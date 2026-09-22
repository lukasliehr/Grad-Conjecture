import QR10OperatorReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Frame

theorem harmonicSeedOperator_operatorConjugation (rho alpha delta parameter angle : ℝ) :
    operatorConjugation 2 2 (harmonicSeedOperator rho alpha delta parameter angle) =
      harmonicSeedOperator rho alpha delta parameter angle := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2 (harmonicSeedOperator rho alpha delta parameter angle
    (cartesianPhysicalConjugation 2 vector)) = _
  rw [harmonicSeedOperator_conjugate, cartesianPhysicalConjugation_involutive]

theorem actualInverseOperator_operatorConjugation (parameter : Seed.Parameters) (angle : ℝ) :
    operatorConjugation 2 2 (Seed.actualInverseOperator parameter angle) =
      Seed.actualInverseOperator parameter angle := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2 (Seed.actualInverseOperator parameter angle
    (cartesianPhysicalConjugation 2 vector)) = _
  rw [actualInverseOperator_conjugate, cartesianPhysicalConjugation_involutive]

theorem operatorConjugation_id (dimension : ℕ) :
    operatorConjugation dimension dimension (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean dimension) := by
  apply ContinuousLinearMap.ext
  intro vector
  exact cartesianPhysicalConjugation_involutive dimension vector

/-- Fourier coefficients of an actual real operator family satisfy the
cell-reversal law. Isometric integral transport does not assume integrability. -/
theorem realOperatorFourierCoefficient (inputDimension outputDimension : ℕ)
    (family : ℝ → OperatorValue inputDimension outputDimension)
    (realFamily : ∀ angle, operatorConjugation inputDimension outputDimension (family angle) =
      family angle) (cell : ℤ) :
    operatorConjugation inputDimension outputDimension
        (((2 * Real.pi : ℝ)⁻¹ : ℂ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
          Complex.exp (-Complex.I * (cell : ℂ) * angle) • family angle) =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-Complex.I * ((-cell : ℤ) : ℂ) * angle) • family angle := by
  rw [operatorConjugation_complex_smul, map_inv₀, Complex.conj_ofReal]
  have transport : operatorConjugation inputDimension outputDimension
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-Complex.I * (cell : ℂ) * angle) • family angle) =
      ∫ angle in (0 : ℝ)..2 * Real.pi,
        operatorConjugation inputDimension outputDimension
          (Complex.exp (-Complex.I * (cell : ℂ) * angle) • family angle) :=
    ((operatorConjugation inputDimension outputDimension).toLinearIsometry.intervalIntegral_comp_comm _).symm
  rw [transport]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  dsimp only
  rw [operatorConjugation_complex_smul, realFamily, ← Complex.exp_conj]
  congr 2
  simp [map_mul]

theorem seedDeviationCell_operatorConjugation (rho alpha delta parameter : ℝ) (cell : ℤ) :
    operatorConjugation 2 2 (seedDeviationCell rho alpha delta parameter cell) =
      seedDeviationCell rho alpha delta parameter (-cell) := by
  apply realOperatorFourierCoefficient 2 2
  intro angle
  rw [map_sub, harmonicSeedOperator_operatorConjugation, operatorConjugation_id]

/-- The three actual seed families M-I, M^-1-I and M' all have the mandatory
conjugate/cell-reversal symmetry; no reality hypothesis is added. -/
theorem actualCells_operatorConjugation (kind : Fin 3) (parameter : Seed.Parameters) (cell : ℤ) :
    operatorConjugation 2 2 (Seed.actualCells kind parameter cell) =
      Seed.actualCells kind parameter (-cell) := by
  fin_cases kind
  · exact seedDeviationCell_operatorConjugation _ _ _ _ cell
  · change operatorConjugation 2 2
        ((2 * (Real.pi : ℂ))⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
          Complex.exp (-Complex.I * (cell : ℂ) * angle) •
            (Seed.actualInverseOperator parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) =
      (2 * (Real.pi : ℂ))⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-Complex.I * ((-cell : ℤ) : ℂ) * angle) •
          (Seed.actualInverseOperator parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
    have identity := realOperatorFourierCoefficient 2 2
      (fun angle => Seed.actualInverseOperator parameter angle -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
      (fun angle => by rw [map_sub, actualInverseOperator_operatorConjugation, operatorConjugation_id]) cell
    simpa only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] using identity
  · change operatorConjugation 2 2 ((Complex.I * (cell : ℂ)) •
        seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell) =
      (Complex.I * ((-cell : ℤ) : ℂ)) •
        seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) (-cell)
    rw [operatorConjugation_complex_smul, seedDeviationCell_operatorConjugation]
    congr 1
    simp [map_mul]

end Grad.CompletedReality
