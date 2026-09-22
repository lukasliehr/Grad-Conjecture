import SeedEnvelope

noncomputable section

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Frame

theorem actual_deviation_bound (phase : PhaseParameters) (grade : ℕ)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (parameter : Parameters)
    (rhoSmall : |parameter 0| ≤ 1) (otherSmall : ∀ index : Fin 3, |parameter index.succ| ≤ radius) :
    Summable (Multipliers.envelopeTerm phase grade (actualCells 0 parameter)) ∧
      Multipliers.envelope phase grade (actualCells 0 parameter) ≤
        (envelopeComparison phase grade * seedDeviationConstant phase.sigma0 radius grade) * |parameter 0| := by
  let coefficient := seedMatrixDeviationCoefficient (seedAdmissible phase) grade
    (parameter 0) (parameter 1) (parameter 2) (parameter 3)
  have realization (cell : ℤ) : coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin =
      actualCells 0 parameter cell := by
    change coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin =
      seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell
    exact seedMatrixDeviation_cell (seedAdmissible phase) grade
      (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell seedOrigin
  have conversion := coefficient_envelope_bound phase grade coefficient (actualCells 0 parameter) realization
  refine ⟨conversion.1, conversion.2.trans ?_⟩
  have bound := seedMatrixDeviation_norm_le (seedAdmissible phase) grade radiusNonnegative rhoSmall
    (otherSmall 0) (otherSmall 1) (otherSmall 2)
  exact (mul_le_mul_of_nonneg_left bound (envelopeComparison_nonnegative phase grade)).trans_eq (mul_assoc _ _ _).symm

theorem actual_derivative_bound (phase : PhaseParameters) (grade : ℕ)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (parameter : Parameters)
    (rhoSmall : |parameter 0| ≤ 1) (otherSmall : ∀ index : Fin 3, |parameter index.succ| ≤ radius) :
    Summable (Multipliers.envelopeTerm phase grade (actualCells 2 parameter)) ∧
      Multipliers.envelope phase grade (actualCells 2 parameter) ≤
        (envelopeComparison phase grade * seedDerivativeConstant phase.sigma0 radius grade) * |parameter 0| := by
  let coefficient := seedDerivativeCoefficient (seedAdmissible phase) grade
    (parameter 0) (parameter 1) (parameter 2) (parameter 3)
  have realization (cell : ℤ) : coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin =
      actualCells 2 parameter cell := by
    rw [seedDerivativeCoefficient_derivative]
    simp [actualCells, derivativeOrder_zeroDerivativeIndexAt, scaledSeedDerivativeCell]
  have conversion := coefficient_envelope_bound phase grade coefficient (actualCells 2 parameter) realization
  refine ⟨conversion.1, conversion.2.trans ?_⟩
  have bound := seedDerivativeCoefficient_norm_le (seedAdmissible phase) grade radiusNonnegative rhoSmall
    (otherSmall 0) (otherSmall 1) (otherSmall 2)
  exact (mul_le_mul_of_nonneg_left bound (envelopeComparison_nonnegative phase grade)).trans_eq (mul_assoc _ _ _).symm

end Grad.Constraints.Seed
