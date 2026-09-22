import GC10Closure

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem weightedCompositionTerm_unweighted {L sigma gamma ell : ℝ}
    (grade : ℕ) {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell first : ℤ) (index : DerivativeIndex grade)
    (split : DerivativeSplit index) (point : ClosedDisk) :
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
        weightedCompositionTerm L sigma gamma ell grade outer.1 first inner.1
          (cell - first) index split point =
      (coefficientDerivative outer first (lowerDerivativeIndex index split) point).comp
        (coefficientDerivative inner (cell - first)
          (upperDerivativeIndex index split) point) := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      ((scaleRatio L sigma gamma ell grade first (cell - first) index split point : ℂ) •
        (outer.1 (first, lowerDerivativeIndex index split) point).comp
          (inner.1 (cell - first, upperDerivativeIndex index split) point)) =
    (((coefficientScale L sigma gamma ell grade first
        (lowerDerivativeIndex index split) point : ℂ)⁻¹) •
      outer.1 (first, lowerDerivativeIndex index split) point).comp
    (((coefficientScale L sigma gamma ell grade (cell - first)
        (upperDerivativeIndex index split) point : ℂ)⁻¹) •
      inner.1 (cell - first, upperDerivativeIndex index split) point)
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  have outputNonzero :
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade cell index point).ne'
  have outerNonzero :
      (coefficientScale L sigma gamma ell grade first
        (lowerDerivativeIndex index split) point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade first
        (lowerDerivativeIndex index split) point).ne'
  have innerNonzero :
      (coefficientScale L sigma gamma ell grade (cell - first)
        (upperDerivativeIndex index split) point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade (cell - first)
        (upperDerivativeIndex index split) point).ne'
  have scalarIdentity :
      (coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹ *
          (scaleRatio L sigma gamma ell grade first (cell - first) index split point : ℂ) =
        (coefficientScale L sigma gamma ell grade first
          (lowerDerivativeIndex index split) point : ℂ)⁻¹ *
        (coefficientScale L sigma gamma ell grade (cell - first)
          (upperDerivativeIndex index split) point : ℂ)⁻¹ := by
    unfold scaleRatio
    rw [show first + (cell - first) = cell by omega]
    push_cast
    field_simp
  rw [scalarIdentity]
  rw [mul_comm]

theorem weightedCompositionTerm_apply_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (point : ClosedDisk) :
    Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split point) := by
  exact ((ContinuousMap.evalCLM ℂ point).hasSum
    (weightedCompositionTerm_summable admissible grade
      outer inner cell index split).hasSum).summable

theorem weightedCompositionCoordinate_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    weightedCompositionCoordinate L sigma gamma ell grade outer inner cell index point =
      ∑ split : DerivativeSplit index,
        (splitMultiplicity index split : ℂ) •
          ∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
            outer first inner (cell - first) index split point := by
  unfold weightedCompositionCoordinate
  change (ContinuousMap.evalCLM ℂ point)
      (∑ split : DerivativeSplit index,
        (splitMultiplicity index split : ℂ) •
          ∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
            outer first inner (cell - first) index split) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  rw [map_smul]
  rw [(ContinuousMap.evalCLM ℂ point).map_tsum
    (weightedCompositionTerm_summable admissible grade
      outer inner cell index split)]
  apply congrArg (fun value : OperatorValue inputDimension outputDimension =>
    (splitMultiplicity index split : ℂ) • value)
  apply tsum_congr
  intro first
  rfl

theorem formalCompositionSplit_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (point : ClosedDisk) :
    Summable (fun first : ℤ =>
      (splitMultiplicity index split : ℂ) •
        (coefficientDerivative outer first (lowerDerivativeIndex index split) point).comp
          (coefficientDerivative inner (cell - first)
            (upperDerivativeIndex index split) point)) := by
  have termSummable := weightedCompositionTerm_apply_summable admissible grade
    outer.1 inner.1 cell index split point
  have scaledSummable := Summable.const_smul
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹)
    (Summable.const_smul (splitMultiplicity index split : ℂ) termSummable)
  refine scaledSummable.congr ?_
  intro first
  simpa only [smul_smul, mul_comm] using
    congrArg (fun value : OperatorValue inputDimension outputDimension =>
      (splitMultiplicity index split : ℂ) • value)
      (weightedCompositionTerm_unweighted grade outer inner cell first index split point)

theorem coefficientComposition_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (coefficientComposition admissible grade outer inner)
        cell index point = formalCompositionDerivative outer inner cell index point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      weightedCompositionCoordinate L sigma gamma ell grade outer.1 inner.1 cell index point =
    ∑' first : ℤ, ∑ split : DerivativeSplit index,
      (splitMultiplicity index split : ℂ) •
        (coefficientDerivative outer first (lowerDerivativeIndex index split) point).comp
          (coefficientDerivative inner (cell - first)
            (upperDerivativeIndex index split) point)
  rw [weightedCompositionCoordinate_apply admissible]
  rw [Finset.smul_sum]
  rw [Summable.tsum_finsetSum (fun split _membership =>
    formalCompositionSplit_summable admissible grade outer inner cell index split point)]
  apply Finset.sum_congr rfl
  intro split _membership
  have termSummable := weightedCompositionTerm_apply_summable admissible grade
    outer.1 inner.1 cell index split point
  have multiplicitySummable :=
    Summable.const_smul (splitMultiplicity index split : ℂ) termSummable
  rw [← Summable.tsum_const_smul
    (splitMultiplicity index split : ℂ) termSummable]
  rw [← Summable.tsum_const_smul
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹)
    multiplicitySummable]
  apply tsum_congr
  intro first
  simpa only [smul_smul, mul_comm] using
    congrArg (fun value : OperatorValue inputDimension outputDimension =>
      (splitMultiplicity index split : ℂ) • value)
      (weightedCompositionTerm_unweighted grade outer inner cell first index split point)

end Grad.GaugeCoefficients.Algebra
