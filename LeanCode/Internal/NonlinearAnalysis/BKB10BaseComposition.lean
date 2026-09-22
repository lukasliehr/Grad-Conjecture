import BKB9CompositionMoments

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

def fullKernelCompositionZeroBoundPair
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (pair : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  fullKernelWeightedEnvelope parameters 0 outer pair.1 *
    fullKernelWeightedEnvelope parameters 0 inner pair.2

theorem fullKernelCompositionZeroBoundPair_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    Summable (fullKernelCompositionZeroBoundPair outer inner) :=
  (fullKernelWeightedEnvelope_summable parameters 0 outer).mul_of_nonneg
    (fullKernelWeightedEnvelope_summable parameters 0 inner)
    (fullKernelWeightedEnvelope_nonnegative parameters 0 outer)
    (fullKernelWeightedEnvelope_nonnegative parameters 0 inner)

theorem fullKernelCompositionWeightedPair_zero_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total middle : ℤ × ℤ) :
    fullKernelCompositionWeightedPair 0 outer inner (total, middle) ≤
      fullKernelCompositionZeroBoundPair outer inner
        (total - middle, middle) := by
  have totalLaw : total - middle + middle = total := sub_add_cancel total middle
  have phaseBound : boundaryCoefficientPhaseCost parameters total ≤
      boundaryCoefficientPhaseCost parameters (total - middle) *
        boundaryCoefficientPhaseCost parameters middle := by
    calc
      boundaryCoefficientPhaseCost parameters total =
          boundaryCoefficientPhaseCost parameters (total - middle + middle) :=
        congrArg (boundaryCoefficientPhaseCost parameters) totalLaw.symm
      _ ≤ _ := boundaryCoefficientPhaseCost_add_le parameters (total - middle) middle
  unfold fullKernelCompositionWeightedPair fullKernelCompositionZeroBoundPair
    fullKernelWeightedEnvelope
  simp only [pow_zero, mul_one]
  apply (mul_le_mul_of_nonneg_right phaseBound
    (mul_nonneg (fullKernelEntryNorm_nonnegative outer (total - middle))
      (fullKernelEntryNorm_nonnegative inner middle))).trans_eq
  ring

theorem fullKernelCompositionMajorant_zero_moment_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    (∑' total : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters total *
        fullKernelCompositionMajorant outer inner total) ≤
      fullKernelMoment parameters 0 outer *
        fullKernelMoment parameters 0 inner := by
  have pairSummable := fullKernelCompositionWeightedPair_summable 0 outer inner
  have independent := fullKernelCompositionZeroBoundPair_summable outer inner
  have reindexed : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      fullKernelCompositionZeroBoundPair outer inner
        (pair.1 - pair.2, pair.2)) :=
    twoFrequencyConvolutionEquiv.summable_iff.mpr independent
  calc
    (∑' total : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters total *
        fullKernelCompositionMajorant outer inner total) =
        ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
          fullKernelCompositionWeightedPair 0 outer inner pair := by
      rw [pairSummable.tsum_prod]
      apply tsum_congr
      intro total
      unfold fullKernelCompositionMajorant fullKernelCompositionWeightedPair
      simp only [pow_zero, mul_one]
      rw [← tsum_mul_left]
    _ ≤ ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
        fullKernelCompositionZeroBoundPair outer inner
          (pair.1 - pair.2, pair.2) :=
      pairSummable.tsum_le_tsum
        (fun pair => fullKernelCompositionWeightedPair_zero_le outer inner
          pair.1 pair.2)
        reindexed
    _ = ∑' pair : (ℤ × ℤ) × (ℤ × ℤ),
        fullKernelCompositionZeroBoundPair outer inner pair :=
      twoFrequencyConvolutionEquiv.tsum_eq
        (fullKernelCompositionZeroBoundPair outer inner)
    _ = _ := by
      unfold fullKernelCompositionZeroBoundPair fullKernelMoment
        fullKernelWeightedEnvelope
      have outerZero := outer.moments 0
      have innerZero := inner.moments 0
      have pair := fullKernelCompositionZeroBoundPair_summable outer inner
      rw [← outerZero.tsum_mul_tsum innerZero pair]

theorem fullKernelComposition_zero_moment_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelMoment parameters 0 (fullKernelComposition outer inner) ≤
      fullKernelMoment parameters 0 outer *
        fullKernelMoment parameters 0 inner := by
  unfold fullKernelMoment
  have first := ((fullKernelComposition outer inner).moments 0).tsum_le_tsum
    (fun total => mul_le_mul_of_nonneg_left
      (fullKernelComposition_entryNorm_le outer inner total)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters total)
        (pow_nonneg (annularFrequency_pos total).le 0)))
    (fullKernelCompositionMajorant_moments outer inner 0)
  apply first.trans
  simpa only [fullKernelMoment, pow_zero, mul_one] using
    fullKernelCompositionMajorant_zero_moment_le outer inner

end Grad.BoundaryKernelAction
