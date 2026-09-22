import QR11SeedCoefficientReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Multipliers
open Grad.GaugeCoefficients.Algebra

theorem operatorConjugation_eval {sourceDimension targetDimension : ℕ}
    (mapping : OperatorValue sourceDimension targetDimension)
    (vector : ComplexEuclidean sourceDimension) :
    operatorConjugation sourceDimension targetDimension mapping
        (cartesianPhysicalConjugation sourceDimension vector) =
      cartesianPhysicalConjugation targetDimension (mapping vector) := by
  change cartesianPhysicalConjugation targetDimension
    (mapping (cartesianPhysicalConjugation sourceDimension
      (cartesianPhysicalConjugation sourceDimension vector))) = _
  rw [cartesianPhysicalConjugation_involutive]

/-- Conjugation of the actual smooth multiplier, using its convergent cell
sum and reversal of the summation index. -/
theorem smoothMultiplier_conjugate {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → OperatorValue sourceDimension targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm parameters grade coefficients))
    (reality : ∀ cell, operatorConjugation sourceDimension targetDimension (coefficients cell) =
      coefficients (-cell)) (field : ACore parameters sourceDimension) :
    cartesianCoreConjugation parameters (smoothMultiplier parameters coefficients summable field) =
      smoothMultiplier parameters coefficients summable (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation targetDimension
      (((smoothMultiplier parameters coefficients summable field).1 (-cell)).value point) = _
  have original := smoothMultiplier_value_hasSum parameters coefficients summable field (-cell) point
  have mapped : HasSum (fun shift : ℤ => cartesianPhysicalConjugation targetDimension
      (coefficients shift ((field.1 (-cell - shift)).value point)))
      (cartesianPhysicalConjugation targetDimension
        (((smoothMultiplier parameters coefficients summable field).1 (-cell)).value point)) :=
    (cartesianPhysicalConjugation targetDimension).toContinuousLinearEquiv.toContinuousLinearMap.hasSum original
  have reindexed := (Equiv.neg ℤ).hasSum_iff.mpr mapped
  have target := smoothMultiplier_value_hasSum parameters coefficients summable
    (cartesianCoreConjugation parameters field) cell point
  have sameTerms : HasSum (fun shift : ℤ => coefficients shift
      (((cartesianCoreConjugation parameters field).1 (cell - shift)).value point))
      (cartesianPhysicalConjugation targetDimension
        (((smoothMultiplier parameters coefficients summable field).1 (-cell)).value point)) := by
    apply reindexed.congr_fun
    intro shift
    change coefficients shift (cartesianPhysicalConjugation sourceDimension
      ((field.1 (-(cell - shift))).value point)) =
      cartesianPhysicalConjugation targetDimension
        (coefficients (-shift) ((field.1 (-cell - -shift)).value point))
    rw [← operatorConjugation_eval, reality, neg_neg]
    rw [show -(cell - shift) = -cell - -shift by omega]
  exact sameTerms.unique target

theorem seedDeviationCore_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (seedDeviationCore parameters parameter inside kind field) =
      seedDeviationCore parameters parameter inside kind (cartesianCoreConjugation parameters field) :=
  smoothMultiplier_conjugate parameters _ _ (actualCells_operatorConjugation kind parameter) field

theorem seedMatrixCore_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (seedMatrixCore parameters parameter inside field) =
      seedMatrixCore parameters parameter inside (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (field + seedDeviationCore parameters parameter inside 0 field) = _
  rw [map_add, seedDeviationCore_conjugate]
  rfl

theorem seedInverseCore_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (seedInverseCore parameters parameter inside field) =
      seedInverseCore parameters parameter inside (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (field + seedDeviationCore parameters parameter inside 1 field) = _
  rw [map_add, seedDeviationCore_conjugate]
  rfl

end Grad.CompletedReality
