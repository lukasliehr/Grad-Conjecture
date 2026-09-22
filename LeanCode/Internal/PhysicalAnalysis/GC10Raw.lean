import GC10TermSums

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem weightedCompositionCoordinate_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ‖weightedCompositionCoordinate L sigma gamma ell grade outer inner cell index‖ ≤
      weightedCompositionMajorant grade outer inner cell index := by
  change ‖∑ split : DerivativeSplit index,
      weightedCompositionSplit L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer inner cell index split‖ ≤
    weightedCompositionMajorant grade outer inner cell index
  calc
    ‖∑ split : DerivativeSplit index,
        weightedCompositionSplit L sigma gamma ell grade inputDimension middleDimension
          outputDimension outer inner cell index split‖
        ≤ ∑ split : DerivativeSplit index,
          ‖weightedCompositionSplit L sigma gamma ell grade inputDimension middleDimension
            outputDimension outer inner cell index split‖ := by
      exact norm_sum_le Finset.univ (fun split : DerivativeSplit index =>
        weightedCompositionSplit L sigma gamma ell grade inputDimension middleDimension
          outputDimension outer inner cell index split)
    _ ≤ ∑ split : DerivativeSplit index,
        weightedCompositionSplitBound grade inputDimension middleDimension outputDimension
          outer inner cell index split := by
      apply Finset.sum_le_sum
      intro split _membership
      exact weightedCompositionSplit_norm_le
        (inputDimension := inputDimension) (middleDimension := middleDimension)
        (outputDimension := outputDimension) admissible grade outer inner cell index split
    _ = weightedCompositionMajorant grade outer inner cell index := by
      unfold weightedCompositionSplitBound weightedCompositionTermBound
        weightedCompositionMajorant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro split _membership
      ring

theorem convolution_majorant_fixed_summable (grade : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (index : DerivativeIndex grade) :
    Summable (fun cell : ℤ => weightedCompositionMajorant grade outer inner cell index) := by
  unfold weightedCompositionMajorant
  apply Summable.mul_left
  have each (split : DerivativeSplit index) :
      Summable (fun cell : ℤ => (splitMultiplicity index split : ℝ) *
        ∑' first : ℤ,
          ‖outer (first, lowerDerivativeIndex index split)‖ *
            ‖inner (cell - first, upperDerivativeIndex index split)‖) :=
    ((convolution_norm_reindexed_summable outer inner
      (lowerDerivativeIndex index split) (upperDerivativeIndex index split)).prod).mul_left _
  exact (hasSum_sum (fun split _membership => (each split).hasSum)).summable

theorem weightedCompositionMajorant_nonnegative (grade : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    0 ≤ weightedCompositionMajorant grade outer inner cell index := by
  unfold weightedCompositionMajorant
  positivity

theorem convolution_majorant_summable (grade : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    Summable (fun pair : ℤ × DerivativeIndex grade =>
      weightedCompositionMajorant grade outer inner pair.1 pair.2) := by
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      weightedCompositionMajorant grade outer inner pair.2 pair.1) := by
    apply (summable_prod_of_nonneg (fun pair =>
      weightedCompositionMajorant_nonnegative grade outer inner pair.2 pair.1)).2
    refine ⟨fun index => convolution_majorant_fixed_summable grade outer inner index, ?_⟩
    exact (hasSum_fintype _).summable
  apply (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp
  change Summable (fun pair : DerivativeIndex grade × ℤ =>
    weightedCompositionMajorant grade outer inner pair.2 pair.1)
  exact swapped

theorem convolution_majorant_index_total_le (grade : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (index : DerivativeIndex grade) :
    (∑' cell : ℤ, weightedCompositionMajorant grade outer inner cell index) ≤
      (Real.sqrt 2) ^ grade *
        (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ)) *
        (‖outer‖ * ‖inner‖) := by
  unfold weightedCompositionMajorant
  rw [tsum_mul_left]
  have each (split : DerivativeSplit index) : Summable (fun cell : ℤ =>
      (splitMultiplicity index split : ℝ) *
        ∑' first : ℤ,
          ‖outer (first, lowerDerivativeIndex index split)‖ *
            ‖inner (cell - first, upperDerivativeIndex index split)‖) :=
    ((convolution_norm_reindexed_summable outer inner
      (lowerDerivativeIndex index split) (upperDerivativeIndex index split)).prod).mul_left _
  rw [Summable.tsum_finsetSum (fun split _membership => each split)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg 2) _)
  calc
    (∑ split : DerivativeSplit index,
        ∑' cell : ℤ, (splitMultiplicity index split : ℝ) *
          ∑' first : ℤ,
            ‖outer (first, lowerDerivativeIndex index split)‖ *
              ‖inner (cell - first, upperDerivativeIndex index split)‖)
        ≤ ∑ split : DerivativeSplit index,
          (splitMultiplicity index split : ℝ) * (‖outer‖ * ‖inner‖) := by
      apply Finset.sum_le_sum
      intro split _membership
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        (convolution_norm_total_le outer inner
          (lowerDerivativeIndex index split) (upperDerivativeIndex index split))
        (Nat.cast_nonneg _)
    _ = (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ)) *
        (‖outer‖ * ‖inner‖) := by rw [Finset.sum_mul]

theorem convolution_majorant_total_le (grade : ℕ)
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    (∑' pair : ℤ × DerivativeIndex grade,
      weightedCompositionMajorant grade outer inner pair.1 pair.2) ≤
        gradeProductConstant grade * ‖outer‖ * ‖inner‖ := by
  have summable := convolution_majorant_summable grade outer inner
  calc
    (∑' pair : ℤ × DerivativeIndex grade,
        weightedCompositionMajorant grade outer inner pair.1 pair.2) =
      ∑' cell : ℤ, ∑' index : DerivativeIndex grade,
        weightedCompositionMajorant grade outer inner cell index := summable.tsum_prod
    _ = ∑' index : DerivativeIndex grade, ∑' cell : ℤ,
        weightedCompositionMajorant grade outer inner cell index := by
      exact (show Summable (Function.uncurry (fun cell : ℤ =>
          fun index : DerivativeIndex grade =>
            weightedCompositionMajorant grade outer inner cell index)) from by
            change Summable (fun pair : ℤ × DerivativeIndex grade =>
              weightedCompositionMajorant grade outer inner pair.1 pair.2)
            exact summable).tsum_comm.symm
    _ = ∑ index : DerivativeIndex grade,
        ∑' cell : ℤ, weightedCompositionMajorant grade outer inner cell index := by
      simp only [tsum_fintype]
    _ ≤ ∑ index : DerivativeIndex grade,
        (Real.sqrt 2) ^ grade *
          (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ)) *
          (‖outer‖ * ‖inner‖) :=
      Finset.sum_le_sum fun index _membership =>
        convolution_majorant_index_total_le grade outer inner index
    _ = gradeProductConstant grade * ‖outer‖ * ‖inner‖ := by
      calc
        (∑ index : DerivativeIndex grade,
            (Real.sqrt 2) ^ grade *
              (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ)) *
              (‖outer‖ * ‖inner‖)) =
            (∑ index : DerivativeIndex grade,
              (Real.sqrt 2) ^ grade *
                (∑ split : DerivativeSplit index,
                  (splitMultiplicity index split : ℝ))) *
              (‖outer‖ * ‖inner‖) := by rw [Finset.sum_mul]
        _ = gradeProductConstant grade * ‖outer‖ * ‖inner‖ := by
          unfold gradeProductConstant
          rw [Finset.mul_sum]
          ring

def rawComposition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    WeightedAmbient grade inputDimension outputDimension := by
  refine ⟨fun pair => weightedCompositionCoordinate L sigma gamma ell grade
    outer inner pair.1 pair.2, ?_⟩
  apply memℓp_gen
  have domination (pair : ℤ × DerivativeIndex grade) :
      ‖weightedCompositionCoordinate L sigma gamma ell grade
        outer inner pair.1 pair.2‖ ≤
        weightedCompositionMajorant grade outer inner pair.1 pair.2 :=
    weightedCompositionCoordinate_norm_le admissible grade outer inner pair.1 pair.2
  have summableNorm : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖weightedCompositionCoordinate L sigma gamma ell grade outer inner pair.1 pair.2‖) :=
    Summable.of_nonneg_of_le
      (fun pair => norm_nonneg (weightedCompositionCoordinate L sigma gamma ell grade
        outer inner pair.1 pair.2)) domination
      (convolution_majorant_summable grade outer inner)
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using summableNorm

theorem rawComposition_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    ‖rawComposition admissible grade outer inner‖ ≤
      gradeProductConstant grade * ‖outer‖ * ‖inner‖ := by
  rw [ambient_norm_formula]
  calc
    (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        ‖rawComposition admissible grade outer inner (cell, index)‖)
        ≤ ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
          weightedCompositionMajorant grade outer inner cell index := by
      apply Finset.sum_le_sum
      intro index _membership
      exact Summable.tsum_le_tsum
        (fun cell => weightedCompositionCoordinate_norm_le admissible grade outer inner cell index)
        ((coordinate_norm_summable (rawComposition admissible grade outer inner) index))
        (convolution_majorant_fixed_summable grade outer inner index)
    _ = ∑' pair : ℤ × DerivativeIndex grade,
        weightedCompositionMajorant grade outer inner pair.1 pair.2 := by
      let summable := convolution_majorant_summable grade outer inner
      calc
        (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
            weightedCompositionMajorant grade outer inner cell index) =
          ∑' index : DerivativeIndex grade, ∑' cell : ℤ,
            weightedCompositionMajorant grade outer inner cell index := by
              simp only [tsum_fintype]
        _ = ∑' cell : ℤ, ∑' index : DerivativeIndex grade,
            weightedCompositionMajorant grade outer inner cell index := by
          exact (show Summable (Function.uncurry (fun cell : ℤ =>
              fun index : DerivativeIndex grade =>
                weightedCompositionMajorant grade outer inner cell index)) from by
                change Summable (fun pair : ℤ × DerivativeIndex grade =>
                  weightedCompositionMajorant grade outer inner pair.1 pair.2)
                exact summable).tsum_comm
        _ = _ := summable.tsum_prod.symm
    _ ≤ _ := convolution_majorant_total_le grade outer inner

end Grad.GaugeCoefficients.Algebra
