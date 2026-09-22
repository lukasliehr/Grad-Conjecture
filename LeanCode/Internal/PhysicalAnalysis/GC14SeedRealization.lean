import GC14SeedLaurent

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def seedCellCLM (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      OperatorValue inputDimension outputDimension :=
  (((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    (ContinuousMap.evalCLM ℂ point)).comp
      ((lp.evalCLM ℂ (fun _ : ℤ × DerivativeIndex grade =>
        C(ClosedDisk, OperatorValue inputDimension outputDimension)) 1 (cell, index)).comp
          (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure.subtypeL)

theorem seedCellCLM_apply {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    seedCellCLM L sigma gamma ell grade inputDimension outputDimension cell index point coefficient =
      coefficientDerivative coefficient cell index point := rfl

theorem seedDerivative_sum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {Index : Type*} (indices : Finset Index)
    (coefficients : Index → Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (∑ item ∈ indices, coefficients item) cell index point =
      ∑ item ∈ indices, coefficientDerivative (coefficients item) cell index point :=
  map_sum (seedCellCLM L sigma gamma ell grade inputDimension outputDimension cell index point) _ _

theorem seedDerivative_tsum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {Index : Type*}
    (coefficients : Index → Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (summability : Summable coefficients)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (∑' item, coefficients item) cell index point =
      ∑' item, coefficientDerivative (coefficients item) cell index point :=
  (seedCellCLM L sigma gamma ell grade inputDimension outputDimension cell index point).map_tsum summability

theorem seedAngleGenerator_realizes (L sigma gamma ell : ℝ) (grade : ℕ)
    (sign alpha delta parameter : ℝ) :
    RealizesSameCoefficient (seedAngleGenerator L sigma gamma ell 0 sign alpha delta parameter)
      (seedAngleGenerator L sigma gamma ell grade sign alpha delta parameter) := by
  intro cell point
  change coefficientDerivative (∑ mode : Fin 5, _) cell
      (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
    coefficientDerivative (∑ mode : Fin 5, _) cell zeroDerivativeIndex point
  rw [seedDerivative_sum, seedDerivative_sum]
  apply Finset.sum_congr rfl
  intro mode _
  simp only [seedConstantCell_derivative, derivativeOrder_zeroDerivativeIndexAt]
  rfl

theorem seedExponential_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (base : Coefficient L sigma gamma ell 0 dimension dimension)
    (graded : Coefficient L sigma gamma ell grade dimension dimension)
    (realizes : RealizesSameCoefficient base graded) :
    RealizesSameCoefficient (seedCoefficientExponential admissible base)
      (seedCoefficientExponential admissible graded) := by
  intro cell point
  change coefficientDerivative (∑' power : ℕ, seedExponentialTerm admissible graded power)
      cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
    coefficientDerivative (∑' power : ℕ, seedExponentialTerm admissible base power)
      cell zeroDerivativeIndex point
  rw [seedDerivative_tsum _ (seedExponentialTerm_norm_summable admissible graded).of_norm,
    seedDerivative_tsum _ (seedExponentialTerm_norm_summable admissible base).of_norm]
  apply tsum_congr
  intro power
  unfold seedExponentialTerm
  rw [coefficientDerivative_smul_apply, coefficientDerivative_smul_apply]
  have each := gradedCoefficientPower_realizes admissible base graded realizes power cell point
  exact congrArg (fun value : OperatorValue dimension dimension =>
    ((power.factorial : ℂ)⁻¹) • value) each

theorem seedAngleExponential_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (sign alpha delta parameter : ℝ) :
    RealizesSameCoefficient (seedAngleExponential admissible 0 sign alpha delta parameter)
      (seedAngleExponential admissible grade sign alpha delta parameter) :=
  seedExponential_realizes admissible _ _
    (seedAngleGenerator_realizes L sigma gamma ell grade sign alpha delta parameter)

def SeedSameValue {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (base : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (graded : Coefficient L sigma gamma ell grade inputDimension outputDimension) : Prop :=
  ∀ (cell : ℤ) (point : ClosedDisk),
    coefficientDerivative graded cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
      coefficientValue base cell point

theorem seedConstantCell_realizes (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (source : ℤ) (value : OperatorValue inputDimension outputDimension) :
    SeedSameValue (seedConstantCell L sigma gamma ell 0 source value)
      (seedConstantCell L sigma gamma ell grade source value) := by
  intro cell point
  change coefficientDerivative _ cell _ point = coefficientDerivative _ cell zeroDerivativeIndex point
  rw [seedConstantCell_derivative, seedConstantCell_derivative]
  simp only [derivativeOrder_zeroDerivativeIndexAt]
  rfl

theorem seedComposition_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension middleDimension outputDimension : ℕ}
    {outerBase : Coefficient L sigma gamma ell 0 middleDimension outputDimension}
    {innerBase : Coefficient L sigma gamma ell 0 inputDimension middleDimension}
    {outer : Coefficient L sigma gamma ell grade middleDimension outputDimension}
    {inner : Coefficient L sigma gamma ell grade inputDimension middleDimension}
    (outerRealizes : SeedSameValue outerBase outer) (innerRealizes : SeedSameValue innerBase inner) :
    SeedSameValue (coefficientComposition admissible 0 outerBase innerBase)
      (coefficientComposition admissible grade outer inner) := by
  intro cell point
  rw [coefficientComposition_derivative]
  unfold formalCompositionDerivative
  rw [coefficientComposition_value]
  apply tsum_congr
  intro first
  rw [derivativeSplit_zeroAt_univ]
  simp only [Finset.sum_singleton, splitMultiplicity_zeroAt, Nat.cast_one,
    one_smul, lowerDerivativeIndex_zeroAt, upperDerivativeIndex_zeroAt]
  rw [outerRealizes, innerRealizes]

end Grad.GaugeCoefficients.Physical.Frame
