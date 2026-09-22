import BKB8KernelOperations

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem fullKernelCompositionWeightedBoundPair_tsum
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    (∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
      fullKernelCompositionWeightedBoundPair moment outer inner pair) =
      2 ^ moment *
        (fullKernelMoment parameters moment outer *
            fullKernelMoment parameters 0 inner +
          fullKernelMoment parameters 0 outer *
            fullKernelMoment parameters moment inner) := by
  have outerMoment := fullKernelWeightedEnvelope_summable parameters moment outer
  have outerZero := fullKernelWeightedEnvelope_summable parameters 0 outer
  have innerMoment := fullKernelWeightedEnvelope_summable parameters moment inner
  have innerZero := fullKernelWeightedEnvelope_summable parameters 0 inner
  have firstPair : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      fullKernelWeightedEnvelope parameters moment outer pair.1 *
        fullKernelWeightedEnvelope parameters 0 inner pair.2) :=
    outerMoment.mul_of_nonneg innerZero
      (fullKernelWeightedEnvelope_nonnegative parameters moment outer)
      (fullKernelWeightedEnvelope_nonnegative parameters 0 inner)
  have secondPair : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      fullKernelWeightedEnvelope parameters 0 outer pair.1 *
        fullKernelWeightedEnvelope parameters moment inner pair.2) :=
    outerZero.mul_of_nonneg innerMoment
      (fullKernelWeightedEnvelope_nonnegative parameters 0 outer)
      (fullKernelWeightedEnvelope_nonnegative parameters moment inner)
  unfold fullKernelCompositionWeightedBoundPair
  rw [tsum_mul_left, Summable.tsum_add firstPair secondPair]
  rw [← outerMoment.tsum_mul_tsum innerZero firstPair,
    ← outerZero.tsum_mul_tsum innerMoment secondPair]
  unfold fullKernelMoment fullKernelWeightedEnvelope
  rfl

theorem fullKernelCompositionMajorant_moment_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    (∑' total : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters total *
        annularFrequency total.1 total.2 ^ moment *
          fullKernelCompositionMajorant outer inner total) ≤
      2 ^ moment *
        (fullKernelMoment parameters moment outer *
            fullKernelMoment parameters 0 inner +
          fullKernelMoment parameters 0 outer *
            fullKernelMoment parameters moment inner) := by
  have pairSummable :=
    fullKernelCompositionWeightedPair_summable moment outer inner
  have boundSummable : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      fullKernelCompositionWeightedBoundPair moment outer inner
        (pair.1 - pair.2, pair.2)) :=
    twoFrequencyConvolutionEquiv.summable_iff.mpr
      (fullKernelCompositionWeightedBoundPair_summable moment outer inner)
  calc
    (∑' total : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters total *
        annularFrequency total.1 total.2 ^ moment *
          fullKernelCompositionMajorant outer inner total) =
        ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
          fullKernelCompositionWeightedPair moment outer inner pair := by
      rw [pairSummable.tsum_prod]
      apply tsum_congr
      intro total
      unfold fullKernelCompositionMajorant fullKernelCompositionWeightedPair
      rw [← tsum_mul_left]
    _ ≤ ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
        fullKernelCompositionWeightedBoundPair moment outer inner
          (pair.1 - pair.2, pair.2) :=
      pairSummable.tsum_le_tsum
        (fun pair => fullKernelCompositionWeightedPair_le moment outer inner
          pair.1 pair.2)
        boundSummable
    _ = ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
        fullKernelCompositionWeightedBoundPair moment outer inner pair :=
      twoFrequencyConvolutionEquiv.tsum_eq
        (fullKernelCompositionWeightedBoundPair moment outer inner)
    _ = _ := fullKernelCompositionWeightedBoundPair_tsum moment outer inner

theorem fullKernelComposition_moment_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelMoment parameters moment (fullKernelComposition outer inner) ≤
      2 ^ moment *
        (fullKernelMoment parameters moment outer *
            fullKernelMoment parameters 0 inner +
          fullKernelMoment parameters 0 outer *
            fullKernelMoment parameters moment inner) := by
  unfold fullKernelMoment
  have first := ((fullKernelComposition outer inner).moments moment).tsum_le_tsum
    (fun total => mul_le_mul_of_nonneg_left
      (fullKernelComposition_entryNorm_le outer inner total)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters total)
        (pow_nonneg (annularFrequency_pos total).le _)))
    (fullKernelCompositionMajorant_moments outer inner moment)
  exact first.trans (fullKernelCompositionMajorant_moment_le moment outer inner)

end Grad.BoundaryKernelAction
