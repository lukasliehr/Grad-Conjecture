import BKB17NeumannTail

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- Literal entries determine a full kernel because `entryNorm` is required
to be their exact input-mode supremum. -/
theorem FullTwoFrequencyKernel.ext_entry
    {sourceDimension targetDimension : ℕ} {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (entries : ∀ shift input, first.entry shift input = second.entry shift input) :
    first = second := by
  have entryEquality : first.entry = second.entry := by
    funext shift input
    exact entries shift input
  have normEquality : first.entryNorm = second.entryNorm := by
    funext shift
    apply le_antisymm
    · apply first.entryNorm_le shift (second.entryNorm shift)
      intro input
      rw [entries shift input]
      exact second.entry_le shift input
    · apply second.entryNorm_le shift (first.entryNorm shift)
      intro input
      rw [← entries shift input]
      exact first.entry_le shift input
  cases first
  cases second
  cases entryEquality
  cases normEquality
  rfl

theorem fullIdentityKernel_comp {dimension : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    fullKernelComposition (fullIdentityKernel parameters dimension) kernel = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry,
    tsum_eq_single total (by
      intro middle distinct
      have nonzero : total - middle ≠ (0, 0) := by
        intro zero
        apply distinct
        have firstCoordinate := congrArg Prod.fst zero
        have secondCoordinate := congrArg Prod.snd zero
        apply Prod.ext <;> dsimp at firstCoordinate secondCoordinate ⊢ <;> omega
      rw [fullIdentityKernel_entry_ne_zero parameters dimension
        (total - middle) (input + middle) nonzero]
      simp)]
  rw [show total - total = (0, 0) by exact sub_self total]
  rw [fullIdentityKernel_entry_zero]
  simp

theorem fullKernel_comp_identity {dimension : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    fullKernelComposition kernel (fullIdentityKernel parameters dimension) = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry,
    tsum_eq_single (0, 0) (by
      intro middle nonzero
      rw [fullIdentityKernel_entry_ne_zero parameters dimension middle input nonzero]
      simp)]
  rw [show total - (0, 0) = total by exact sub_zero total,
    show input + (0, 0) = input by exact add_zero input]
  rw [fullIdentityKernel_entry_zero]
  simp

theorem fullKernelComposition_add_outer
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition (fullKernelAdd first second) inner =
      fullKernelAdd (fullKernelComposition first inner)
        (fullKernelComposition second inner) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelAdd_entry,
    fullKernelComposition_entry, fullKernelComposition_entry]
  calc
    (∑' middle, ((fullKernelAdd first second).entry (total - middle)
        (input + middle)).comp (inner.entry middle input)) =
        ∑' middle, (
          fullKernelCompositionTerm first inner total middle input +
            fullKernelCompositionTerm second inner total middle input) := by
      apply tsum_congr
      intro middle
      unfold fullKernelCompositionTerm
      rw [fullKernelAdd_entry]
      exact ContinuousLinearMap.add_comp _ _ _
    _ = _ := (fullKernelCompositionTerm_summable first inner total input).tsum_add
      (fullKernelCompositionTerm_summable second inner total input)

theorem fullKernelComposition_add_inner
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (first second : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition outer (fullKernelAdd first second) =
      fullKernelAdd (fullKernelComposition outer first)
        (fullKernelComposition outer second) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelAdd_entry,
    fullKernelComposition_entry, fullKernelComposition_entry]
  calc
    (∑' middle, (outer.entry (total - middle) (input + middle)).comp
        ((fullKernelAdd first second).entry middle input)) =
        ∑' middle, (
          fullKernelCompositionTerm outer first total middle input +
            fullKernelCompositionTerm outer second total middle input) := by
      apply tsum_congr
      intro middle
      unfold fullKernelCompositionTerm
      rw [fullKernelAdd_entry]
      exact ContinuousLinearMap.comp_add _ _ _
    _ = _ := (fullKernelCompositionTerm_summable outer first total input).tsum_add
      (fullKernelCompositionTerm_summable outer second total input)

theorem fullKernelComposition_neg_outer
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition (fullKernelNeg outer) inner =
      fullKernelNeg (fullKernelComposition outer inner) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelNeg_entry,
    fullKernelComposition_entry]
  calc
    (∑' middle, ((fullKernelNeg outer).entry (total - middle)
        (input + middle)).comp (inner.entry middle input)) =
        ∑' middle, -fullKernelCompositionTerm outer inner total middle input := by
      apply tsum_congr
      intro middle
      unfold fullKernelCompositionTerm
      rw [fullKernelNeg_entry]
      exact ContinuousLinearMap.neg_comp _ _
    _ = _ := tsum_neg

theorem fullKernelComposition_neg_inner
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition outer (fullKernelNeg inner) =
      fullKernelNeg (fullKernelComposition outer inner) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelNeg_entry,
    fullKernelComposition_entry]
  calc
    (∑' middle, (outer.entry (total - middle) (input + middle)).comp
        ((fullKernelNeg inner).entry middle input)) =
        ∑' middle, -fullKernelCompositionTerm outer inner total middle input := by
      apply tsum_congr
      intro middle
      unfold fullKernelCompositionTerm
      rw [fullKernelNeg_entry]
      exact ContinuousLinearMap.comp_neg _ _
    _ = _ := tsum_neg

end Grad.BoundaryKernelAction
