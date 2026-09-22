import BKB6KernelWeights

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

def fullKernelCompositionTerm {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total middle input : ℤ × ℤ) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  (outer.entry (total - middle) (input + middle)).comp
    (inner.entry middle input)

def fullKernelCompositionMajorant {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total : ℤ × ℤ) : ℝ :=
  ∑' middle : ℤ × ℤ,
    outer.entryNorm (total - middle) * inner.entryNorm middle

theorem fullKernelNormProduct_pair_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      outer.entryNorm (pair.1 - pair.2) * inner.entryNorm pair.2) := by
  have independent : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      outer.entryNorm pair.1 * inner.entryNorm pair.2) :=
    (fullKernelEntryNorm_summable parameters outer).mul_of_nonneg
      (fullKernelEntryNorm_summable parameters inner)
      (fullKernelEntryNorm_nonnegative outer)
      (fullKernelEntryNorm_nonnegative inner)
  exact twoFrequencyConvolutionEquiv.summable_iff.mpr independent

theorem fullKernelNormProduct_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total : ℤ × ℤ) :
    Summable (fun middle : ℤ × ℤ =>
      outer.entryNorm (total - middle) * inner.entryNorm middle) :=
  (fullKernelNormProduct_pair_summable outer inner).prod_factor total

theorem fullKernelCompositionTerm_norm_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total middle input : ℤ × ℤ) :
    ‖fullKernelCompositionTerm outer inner total middle input‖ ≤
      outer.entryNorm (total - middle) * inner.entryNorm middle := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (outer.entry_le _ _) (inner.entry_le _ _)
      (norm_nonneg _) (fullKernelEntryNorm_nonnegative outer _))

theorem fullKernelCompositionTerm_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total input : ℤ × ℤ) :
    Summable (fun middle : ℤ × ℤ =>
      fullKernelCompositionTerm outer inner total middle input) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun middle => fullKernelCompositionTerm_norm_le outer inner total middle input)
    (fullKernelNormProduct_summable outer inner total)

def fullKernelCompositionEntry
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total input : ℤ × ℤ) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  ∑' middle : ℤ × ℤ,
    fullKernelCompositionTerm outer inner total middle input

theorem fullKernelCompositionEntry_norm_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total input : ℤ × ℤ) :
    ‖fullKernelCompositionEntry outer inner total input‖ ≤
      fullKernelCompositionMajorant outer inner total := by
  exact (norm_tsum_le_tsum_norm
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun middle => fullKernelCompositionTerm_norm_le outer inner total middle input)
      (fullKernelNormProduct_summable outer inner total))).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun middle => fullKernelCompositionTerm_norm_le outer inner total middle input)
      (fullKernelNormProduct_summable outer inner total)).tsum_le_tsum
      (fun middle => fullKernelCompositionTerm_norm_le outer inner total middle input)
      (fullKernelNormProduct_summable outer inner total))

theorem fullKernelCompositionMajorant_nonnegative
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total : ℤ × ℤ) :
    0 ≤ fullKernelCompositionMajorant outer inner total := by
  exact tsum_nonneg fun middle => mul_nonneg
    (fullKernelEntryNorm_nonnegative outer (total - middle))
    (fullKernelEntryNorm_nonnegative inner middle)

def fullKernelCompositionWeightedPair
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (pair : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  boundaryCoefficientPhaseCost parameters pair.1 *
    annularFrequency pair.1.1 pair.1.2 ^ moment *
      (outer.entryNorm (pair.1 - pair.2) * inner.entryNorm pair.2)

def fullKernelCompositionWeightedBoundPair
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (pair : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  2 ^ moment *
    (fullKernelWeightedEnvelope parameters moment outer pair.1 *
        fullKernelWeightedEnvelope parameters 0 inner pair.2 +
      fullKernelWeightedEnvelope parameters 0 outer pair.1 *
        fullKernelWeightedEnvelope parameters moment inner pair.2)

theorem fullKernelCompositionWeightedBoundPair_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    Summable (fullKernelCompositionWeightedBoundPair moment outer inner) := by
  apply Summable.mul_left
  exact ((fullKernelWeightedEnvelope_summable parameters moment outer).mul_of_nonneg
      (fullKernelWeightedEnvelope_summable parameters 0 inner)
      (fullKernelWeightedEnvelope_nonnegative parameters moment outer)
      (fullKernelWeightedEnvelope_nonnegative parameters 0 inner)).add
    ((fullKernelWeightedEnvelope_summable parameters 0 outer).mul_of_nonneg
      (fullKernelWeightedEnvelope_summable parameters moment inner)
      (fullKernelWeightedEnvelope_nonnegative parameters 0 outer)
      (fullKernelWeightedEnvelope_nonnegative parameters moment inner))

theorem fullKernelCompositionWeightedPair_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total middle : ℤ × ℤ) :
    fullKernelCompositionWeightedPair moment outer inner (total, middle) ≤
      fullKernelCompositionWeightedBoundPair moment outer inner
        (total - middle, middle) := by
  let first := total - middle
  have totalLaw : first + middle = total := by
    dsimp only [first]
    exact sub_add_cancel total middle
  have phaseBound : boundaryCoefficientPhaseCost parameters total ≤
      boundaryCoefficientPhaseCost parameters first *
        boundaryCoefficientPhaseCost parameters middle := by
    rw [← totalLaw]
    exact boundaryCoefficientPhaseCost_add_le parameters first middle
  have frequencyBound : annularFrequency total.1 total.2 ^ moment ≤
      2 ^ moment *
        (annularFrequency first.1 first.2 ^ moment +
          annularFrequency middle.1 middle.2 ^ moment) := by
    rw [← totalLaw]
    exact annularFrequency_add_pow_le moment first middle
  have weightedBound :
      boundaryCoefficientPhaseCost parameters total *
          annularFrequency total.1 total.2 ^ moment ≤
        (boundaryCoefficientPhaseCost parameters first *
          boundaryCoefficientPhaseCost parameters middle) *
          (2 ^ moment *
            (annularFrequency first.1 first.2 ^ moment +
              annularFrequency middle.1 middle.2 ^ moment)) :=
    mul_le_mul phaseBound frequencyBound
      (pow_nonneg (annularFrequency_pos total).le _)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters first)
        (boundaryCoefficientPhaseCost_nonnegative parameters middle))
  unfold fullKernelCompositionWeightedPair fullKernelCompositionWeightedBoundPair
  dsimp only [first] at totalLaw phaseBound frequencyBound weightedBound ⊢
  apply (mul_le_mul_of_nonneg_right weightedBound
    (mul_nonneg
      (fullKernelEntryNorm_nonnegative outer (total - middle))
      (fullKernelEntryNorm_nonnegative inner middle))).trans_eq
  unfold fullKernelWeightedEnvelope
  simp only [pow_zero, mul_one]
  ring

theorem fullKernelCompositionWeightedPair_summable
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (moment : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    Summable (fullKernelCompositionWeightedPair moment outer inner) := by
  have reindexed : Summable (fun pair : (ℤ × ℤ) × (ℤ × ℤ) =>
      fullKernelCompositionWeightedBoundPair moment outer inner
        (pair.1 - pair.2, pair.2)) :=
    twoFrequencyConvolutionEquiv.summable_iff.mpr
      (fullKernelCompositionWeightedBoundPair_summable moment outer inner)
  exact Summable.of_nonneg_of_le
    (fun pair => mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters pair.1)
        (pow_nonneg (annularFrequency_pos pair.1).le _))
      (mul_nonneg (fullKernelEntryNorm_nonnegative outer (pair.1 - pair.2))
        (fullKernelEntryNorm_nonnegative inner pair.2)))
    (fun pair => fullKernelCompositionWeightedPair_le moment outer inner pair.1 pair.2)
    reindexed

theorem fullKernelCompositionMajorant_moments
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (moment : ℕ) :
    Summable (fun total : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters total *
        annularFrequency total.1 total.2 ^ moment *
          fullKernelCompositionMajorant outer inner total) := by
  have pairSummable :=
    fullKernelCompositionWeightedPair_summable moment outer inner
  apply pairSummable.prod.congr
  intro total
  unfold fullKernelCompositionMajorant fullKernelCompositionWeightedPair
  rw [← tsum_mul_left]

/-- AE7's exact full input-mode-dependent kernel product. -/
def fullKernelComposition {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    FullTwoFrequencyKernel parameters inputDimension outputDimension :=
  fullKernelOfEntries parameters
    (fullKernelCompositionEntry outer inner)
    (fullKernelCompositionMajorant outer inner)
    (fullKernelCompositionEntry_norm_le outer inner)
    (fullKernelCompositionMajorant_moments outer inner)

@[simp] theorem fullKernelComposition_entry
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total input : ℤ × ℤ) :
    (fullKernelComposition outer inner).entry total input =
      ∑' middle : ℤ × ℤ,
        (outer.entry (total - middle) (input + middle)).comp
          (inner.entry middle input) := rfl

theorem fullKernelComposition_entryNorm_le
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (total : ℤ × ℤ) :
    (fullKernelComposition outer inner).entryNorm total ≤
      fullKernelCompositionMajorant outer inner total :=
  fullKernelOfEntries_entryNorm_le parameters
    (fullKernelCompositionEntry outer inner)
    (fullKernelCompositionMajorant outer inner)
    (fullKernelCompositionEntry_norm_le outer inner)
    (fullKernelCompositionMajorant_moments outer inner) total

end Grad.BoundaryKernelAction
