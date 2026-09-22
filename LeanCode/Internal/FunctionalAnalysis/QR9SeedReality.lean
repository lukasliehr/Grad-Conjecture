import QR8Consumer

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame

/-- Actual rectangular operators with real entries commute with ordinary
physical conjugation, independently of their Fourier presentation. -/
theorem realMatrixEmbedding_conjugate (inputDimension outputDimension : ℕ)
    (coefficients : Fin (inputDimension * outputDimension) → ℝ)
    (vector : ComplexEuclidean inputDimension) :
    cartesianPhysicalConjugation outputDimension
        (matrixEmbedding inputDimension outputDimension
          (WithLp.toLp 2 (fun index => (coefficients index : ℂ))) vector) =
      matrixEmbedding inputDimension outputDimension
        (WithLp.toLp 2 (fun index => (coefficients index : ℂ)))
        (cartesianPhysicalConjugation inputDimension vector) := by
  apply PiLp.ext
  intro row
  change conj (matrixEmbedding inputDimension outputDimension _ vector row) = _
  simp only [matrixEmbedding_apply]
  change conj (∑ column : Fin inputDimension,
      vector column * (coefficients (finProdFinEquiv (column, row)) : ℂ)) =
    ∑ column : Fin inputDimension,
      conj (vector column) * (coefficients (finProdFinEquiv (column, row)) : ℂ)
  simp only [map_sum, map_mul, Complex.conj_ofReal]

theorem harmonicSeedOperator_conjugate (rho alpha delta parameter angle : ℝ)
    (vector : ComplexEuclidean 2) :
    cartesianPhysicalConjugation 2 (harmonicSeedOperator rho alpha delta parameter angle vector) =
      harmonicSeedOperator rho alpha delta parameter angle (cartesianPhysicalConjugation 2 vector) :=
  realMatrixEmbedding_conjugate 2 2 _ vector

theorem actualInverseOperator_conjugate (parameter : Seed.Parameters) (angle : ℝ)
    (vector : ComplexEuclidean 2) :
    cartesianPhysicalConjugation 2 (Seed.actualInverseOperator parameter angle vector) =
      Seed.actualInverseOperator parameter angle (cartesianPhysicalConjugation 2 vector) :=
  realMatrixEmbedding_conjugate 2 2 _ vector

end Grad.CompletedReality
