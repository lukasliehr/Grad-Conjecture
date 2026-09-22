import GC10Convolution

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem convolution_norm_fixed_summable
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (outerIndex innerIndex : DerivativeIndex grade) :
    Summable (fun first : ℤ =>
      ‖outer (first, outerIndex)‖ * ‖inner (cell - first, innerIndex)‖) :=
  (convolution_norm_reindexed_summable outer inner outerIndex innerIndex).prod_factor cell

theorem weightedCompositionTerm_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    Summable (fun first : ℤ =>
      ‖weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split‖) := by
  have domination (first : ℤ) :
      ‖weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split‖ ≤
      (Real.sqrt 2) ^ grade *
        (‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖) := by
    simpa only [mul_assoc] using
      weightedCompositionTerm_norm admissible grade
        outer first inner (cell - first) index split
  exact Summable.of_nonneg_of_le (fun first => norm_nonneg
      (weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split)) domination
      ((convolution_norm_fixed_summable outer inner cell
      (lowerDerivativeIndex index split) (upperDerivativeIndex index split)).mul_left
        ((Real.sqrt 2) ^ grade))

theorem weightedCompositionTerm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split) := by
  apply ContinuousMap.summable_of_locally_summable_norm
  intro compact
  have majorantSummable : Summable (fun first : ℤ =>
      (Real.sqrt 2) ^ grade *
        (‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖)) :=
    (convolution_norm_fixed_summable outer inner cell
      (lowerDerivativeIndex index split)
      (upperDerivativeIndex index split)).mul_left ((Real.sqrt 2) ^ grade)
  apply Summable.of_nonneg_of_le
    (fun first : ℤ => norm_nonneg
      ((weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split).restrict compact))
    (fun first : ℤ => by
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro point
      exact (ContinuousMap.norm_coe_le_norm
        (weightedCompositionTerm L sigma gamma ell grade
          outer first inner (cell - first) index split) point).trans
        (by
          simpa only [mul_assoc] using
            (weightedCompositionTerm_norm admissible grade
              outer first inner (cell - first) index split)))
    majorantSummable

def weightedCompositionTermSum (L sigma gamma ell : ℝ) (grade : ℕ)
    (inputDimension middleDimension outputDimension : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  ∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
    outer first inner (cell - first) index split

def weightedCompositionTermBound (grade : ℕ)
    (inputDimension middleDimension outputDimension : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) : ℝ :=
  (Real.sqrt 2) ^ grade *
    ∑' first : ℤ,
      ‖outer (first, lowerDerivativeIndex index split)‖ *
        ‖inner (cell - first, upperDerivativeIndex index split)‖

theorem weightedCompositionTerm_tsum_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ‖weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer inner cell index split‖ ≤
      weightedCompositionTermBound grade inputDimension middleDimension outputDimension
        outer inner cell index split := by
  let term : ℤ → ContinuousMap ClosedDisk
      (OperatorValue inputDimension outputDimension) := fun first =>
    weightedCompositionTerm L sigma gamma ell grade
      outer first inner (cell - first) index split
  have termNormSummable : Summable (fun first : ℤ => ‖term first‖) := by
    simpa only [term] using
      weightedCompositionTerm_norm_summable
        (inputDimension := inputDimension) (middleDimension := middleDimension)
        (outputDimension := outputDimension) admissible grade outer inner cell index split
  have majorantSummable : Summable (fun first : ℤ =>
      (Real.sqrt 2) ^ grade *
        (‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖)) :=
    (convolution_norm_fixed_summable outer inner cell
      (lowerDerivativeIndex index split)
      (upperDerivativeIndex index split)).mul_left ((Real.sqrt 2) ^ grade)
  have domination (first : ℤ) : ‖term first‖ ≤
      (Real.sqrt 2) ^ grade *
        (‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖) := by
    simpa only [term, mul_assoc] using
      weightedCompositionTerm_norm admissible grade
        outer first inner (cell - first) index split
  change ‖∑' first : ℤ, term first‖ ≤
    (Real.sqrt 2) ^ grade *
      ∑' first : ℤ,
        ‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖
  calc
    ‖∑' first : ℤ, term first‖ ≤ ∑' first : ℤ, ‖term first‖ :=
      @norm_tsum_le_tsum_norm ℤ
        (ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension)) _
          term termNormSummable
    _ ≤ ∑' first : ℤ, (Real.sqrt 2) ^ grade *
          (‖outer (first, lowerDerivativeIndex index split)‖ *
            ‖inner (cell - first, upperDerivativeIndex index split)‖) :=
      Summable.tsum_le_tsum
        (f := fun first : ℤ => ‖term first‖)
        (g := fun first : ℤ =>
          (Real.sqrt 2) ^ grade *
            (‖outer (first, lowerDerivativeIndex index split)‖ *
              ‖inner (cell - first, upperDerivativeIndex index split)‖))
        domination termNormSummable majorantSummable
    _ = _ := tsum_mul_left

def weightedCompositionSplit (L sigma gamma ell : ℝ) (grade : ℕ)
    (inputDimension middleDimension outputDimension : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  (splitMultiplicity index split : ℂ) •
    weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
      outputDimension outer inner cell index split

def weightedCompositionSplitBound (grade : ℕ)
    (inputDimension middleDimension outputDimension : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) : ℝ :=
  (splitMultiplicity index split : ℝ) *
    weightedCompositionTermBound grade inputDimension middleDimension outputDimension
      outer inner cell index split

theorem weightedCompositionSplit_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ‖weightedCompositionSplit L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer inner cell index split‖ ≤
      weightedCompositionSplitBound grade inputDimension middleDimension outputDimension
        outer inner cell index split := by
  let termSum := weightedCompositionTermSum L sigma gamma ell grade inputDimension
    middleDimension outputDimension outer inner cell index split
  change ‖(splitMultiplicity index split : ℂ) • termSum‖ ≤
    (splitMultiplicity index split : ℝ) *
      weightedCompositionTermBound grade inputDimension middleDimension outputDimension
        outer inner cell index split
  calc
    ‖(splitMultiplicity index split : ℂ) • termSum‖
        ≤ ‖(splitMultiplicity index split : ℂ)‖ *
            ‖termSum‖ :=
      (ContinuousMap.norm_le
        ((splitMultiplicity index split : ℂ) • termSum)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun point => by
          change ‖(splitMultiplicity index split : ℂ) • termSum point‖ ≤ _
          exact (norm_smul_le (splitMultiplicity index split : ℂ) (termSum point)).trans
            (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm termSum point)
              (norm_nonneg _))
    _ = (splitMultiplicity index split : ℝ) *
            ‖termSum‖ := by
          rw [Complex.norm_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weightedCompositionTerm_tsum_norm_le
        (inputDimension := inputDimension) (middleDimension := middleDimension)
        (outputDimension := outputDimension) admissible grade outer inner cell index split)
      (Nat.cast_nonneg _)

end Grad.GaugeCoefficients.Algebra
