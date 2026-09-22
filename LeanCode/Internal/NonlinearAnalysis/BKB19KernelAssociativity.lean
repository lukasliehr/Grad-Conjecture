import BKB18KernelAlgebra

noncomputable section

set_option maxHeartbeats 2400000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

private abbrev KernelShift := ℤ × ℤ

/-- Reindex three independent displacement shifts by their total and their
first two shifts. -/
def fullKernelTripleEquiv :
    (KernelShift × (KernelShift × KernelShift)) ≃
      ((KernelShift × KernelShift) × KernelShift) where
  toFun pair := ((pair.2.1, pair.2.2), pair.1 - pair.2.1 - pair.2.2)
  invFun triple := (triple.1.1 + triple.1.2 + triple.2, triple.1)
  left_inv pair := by
    rcases pair with ⟨total, ⟨first, second⟩⟩
    apply Prod.ext
    · ext <;> dsimp <;> ring
    · rfl
  right_inv triple := by
    rcases triple with ⟨⟨first, second⟩, third⟩
    apply Prod.ext
    · rfl
    · ext <;> dsimp <;> ring

theorem fullKernelTripleNorm_summable
    {inputDimension firstMiddleDimension secondMiddleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first : FullTwoFrequencyKernel parameters secondMiddleDimension outputDimension)
    (second : FullTwoFrequencyKernel parameters firstMiddleDimension secondMiddleDimension)
    (third : FullTwoFrequencyKernel parameters inputDimension firstMiddleDimension) :
    Summable (fun triple : (KernelShift × KernelShift) × KernelShift =>
      first.entryNorm triple.1.1 * second.entryNorm triple.1.2 *
        third.entryNorm triple.2) := by
  have firstSummable := fullKernelEntryNorm_summable parameters first
  have secondSummable := fullKernelEntryNorm_summable parameters second
  have thirdSummable := fullKernelEntryNorm_summable parameters third
  have pairSummable : Summable (fun pair : KernelShift × KernelShift =>
      first.entryNorm pair.1 * second.entryNorm pair.2) :=
    firstSummable.mul_of_nonneg secondSummable
      (fullKernelEntryNorm_nonnegative first)
      (fullKernelEntryNorm_nonnegative second)
  exact pairSummable.mul_of_nonneg thirdSummable
    (fun pair => mul_nonneg
      (fullKernelEntryNorm_nonnegative first pair.1)
      (fullKernelEntryNorm_nonnegative second pair.2))
    (fullKernelEntryNorm_nonnegative third)

theorem fullKernelTripleNorm_fixed_summable
    {inputDimension firstMiddleDimension secondMiddleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first : FullTwoFrequencyKernel parameters secondMiddleDimension outputDimension)
    (second : FullTwoFrequencyKernel parameters firstMiddleDimension secondMiddleDimension)
    (third : FullTwoFrequencyKernel parameters inputDimension firstMiddleDimension)
    (total : KernelShift) :
    Summable (fun pair : KernelShift × KernelShift =>
      first.entryNorm pair.1 * second.entryNorm pair.2 *
        third.entryNorm (total - pair.1 - pair.2)) := by
  have reindexed := fullKernelTripleEquiv.summable_iff.mpr
    (fullKernelTripleNorm_summable first second third)
  exact reindexed.prod_factor total

def fullKernelTripleTerm
    {inputDimension firstMiddleDimension secondMiddleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first : FullTwoFrequencyKernel parameters secondMiddleDimension outputDimension)
    (second : FullTwoFrequencyKernel parameters firstMiddleDimension secondMiddleDimension)
    (third : FullTwoFrequencyKernel parameters inputDimension firstMiddleDimension)
    (total input : KernelShift) (pair : KernelShift × KernelShift) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  ((first.entry pair.1 (input + (total - pair.1))).comp
    (second.entry pair.2 (input + (total - pair.1 - pair.2)))).comp
      (third.entry (total - pair.1 - pair.2) input)

theorem fullKernelTripleTerm_summable
    {inputDimension firstMiddleDimension secondMiddleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first : FullTwoFrequencyKernel parameters secondMiddleDimension outputDimension)
    (second : FullTwoFrequencyKernel parameters firstMiddleDimension secondMiddleDimension)
    (third : FullTwoFrequencyKernel parameters inputDimension firstMiddleDimension)
    (total input : KernelShift) :
    Summable (fullKernelTripleTerm first second third total input) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun pair => norm_nonneg _)
    (fun pair => ?_) (fullKernelTripleNorm_fixed_summable first second third total)
  unfold fullKernelTripleTerm
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul
          (first.entry_le pair.1 _)
          (second.entry_le pair.2 _)
          (norm_nonneg _)
          (fullKernelEntryNorm_nonnegative first pair.1)))
      (third.entry_le (total - pair.1 - pair.2) input)
      (norm_nonneg _)
      (mul_nonneg
        (fullKernelEntryNorm_nonnegative first pair.1)
        (fullKernelEntryNorm_nonnegative second pair.2)))

def fullKernelLeftAssocEquiv (total : KernelShift) :
    (KernelShift × KernelShift) ≃ (KernelShift × KernelShift) where
  toFun pair := (total - pair.1 - pair.2, pair.2)
  invFun pair := (total - pair.1 - pair.2, pair.2)
  left_inv pair := by
    apply Prod.ext
    · ext <;> dsimp <;> ring
    · rfl
  right_inv pair := by
    apply Prod.ext
    · ext <;> dsimp <;> ring
    · rfl

def fullKernelRightAssocEquiv (total : KernelShift) :
    (KernelShift × KernelShift) ≃ (KernelShift × KernelShift) where
  toFun pair := (total - pair.1, pair.1 - pair.2)
  invFun pair := (total - pair.1, total - pair.1 - pair.2)
  left_inv pair := by
    apply Prod.ext <;> (ext <;> dsimp <;> ring)
  right_inv pair := by
    apply Prod.ext <;> (ext <;> dsimp <;> ring)

theorem fullKernelComposition_assoc
    {inputDimension firstMiddleDimension secondMiddleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first : FullTwoFrequencyKernel parameters secondMiddleDimension outputDimension)
    (second : FullTwoFrequencyKernel parameters firstMiddleDimension secondMiddleDimension)
    (third : FullTwoFrequencyKernel parameters inputDimension firstMiddleDimension) :
    fullKernelComposition (fullKernelComposition first second) third =
      fullKernelComposition first (fullKernelComposition second third) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelComposition_entry]
  simp_rw [fullKernelComposition_entry]
  have normalizedSummable :=
    fullKernelTripleTerm_summable first second third total input
  have leftPairSummable : Summable (fun pair : KernelShift × KernelShift =>
      ((first.entry (total - pair.1 - pair.2) (input + pair.1 + pair.2)).comp
        (second.entry pair.2 (input + pair.1))).comp
          (third.entry pair.1 input)) := by
    apply ((fullKernelLeftAssocEquiv total).summable_iff.mpr
      normalizedSummable).congr
    intro pair
    change fullKernelTripleTerm first second third total input
        (fullKernelLeftAssocEquiv total pair) = _
    unfold fullKernelTripleTerm fullKernelLeftAssocEquiv
    simp only [Equiv.coe_fn_mk]
    have firstInput :
        input + (total - (total - pair.1 - pair.2)) =
          input + pair.1 + pair.2 := by
      ext <;> dsimp <;> ring
    have tailShift :
        total - (total - pair.1 - pair.2) - pair.2 = pair.1 := by
      ext <;> dsimp <;> ring
    rw [firstInput, tailShift]
  have rightPairSummable : Summable (fun pair : KernelShift × KernelShift =>
      (first.entry (total - pair.1) (input + pair.1)).comp
        ((second.entry (pair.1 - pair.2) (input + pair.2)).comp
          (third.entry pair.2 input))) := by
    apply ((fullKernelRightAssocEquiv total).summable_iff.mpr
      normalizedSummable).congr
    intro pair
    change fullKernelTripleTerm first second third total input
        (fullKernelRightAssocEquiv total pair) = _
    unfold fullKernelTripleTerm fullKernelRightAssocEquiv
    simp only [Equiv.coe_fn_mk]
    have outerInput :
        input + (total - (total - pair.1)) = input + pair.1 := by
      ext <;> dsimp <;> ring
    have innerShift :
        total - (total - pair.1) - (pair.1 - pair.2) = pair.2 := by
      ext <;> dsimp <;> ring
    rw [outerInput, innerShift]
    apply ContinuousLinearMap.ext
    intro value
    rfl
  calc
    (∑' outer : KernelShift,
        (∑' middle : KernelShift,
          (first.entry (total - outer - middle) (input + outer + middle)).comp
            (second.entry middle (input + outer))).comp
              (third.entry outer input)) =
        ∑' outer : KernelShift, ∑' middle : KernelShift,
          ((first.entry (total - outer - middle) (input + outer + middle)).comp
            (second.entry middle (input + outer))).comp
              (third.entry outer input) := by
      apply tsum_congr
      intro outer
      let composition := ContinuousLinearMap.compL ℂ
        (ComplexEuclidean inputDimension) (ComplexEuclidean firstMiddleDimension)
          (ComplexEuclidean outputDimension)
      let composeRight :=
        (ContinuousLinearMap.apply ℂ
          (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
          (third.entry outer input)).comp composition
      change composeRight (∑' middle : KernelShift,
          (first.entry ((total - outer) - middle)
            ((input + outer) + middle)).comp
              (second.entry middle (input + outer))) =
        ∑' middle : KernelShift, composeRight
          ((first.entry ((total - outer) - middle)
            ((input + outer) + middle)).comp
              (second.entry middle (input + outer)))
      exact composeRight.map_tsum
        (fullKernelCompositionTerm_summable first second
          (total - outer) (input + outer))
    _ = ∑' pair : KernelShift × KernelShift,
        ((first.entry (total - pair.1 - pair.2) (input + pair.1 + pair.2)).comp
          (second.entry pair.2 (input + pair.1))).comp
            (third.entry pair.1 input) := leftPairSummable.tsum_prod.symm
    _ = ∑' pair : KernelShift × KernelShift,
          fullKernelTripleTerm first second third total input
            (fullKernelLeftAssocEquiv total pair) := by
      apply tsum_congr
      intro pair
      unfold fullKernelTripleTerm fullKernelLeftAssocEquiv
      simp only [Equiv.coe_fn_mk]
      have firstInput :
          input + (total - (total - pair.1 - pair.2)) =
            input + pair.1 + pair.2 := by
        ext <;> dsimp <;> ring
      have tailShift :
          total - (total - pair.1 - pair.2) - pair.2 = pair.1 := by
        ext <;> dsimp <;> ring
      rw [firstInput, tailShift]
    _ = ∑' pair : KernelShift × KernelShift,
          fullKernelTripleTerm first second third total input pair :=
      (fullKernelLeftAssocEquiv total).tsum_eq
        (fullKernelTripleTerm first second third total input)
    _ = ∑' pair : KernelShift × KernelShift,
        (first.entry pair.1 (input + (total - pair.1))).comp
          ((second.entry pair.2 (input + (total - pair.1 - pair.2))).comp
            (third.entry (total - pair.1 - pair.2) input)) := by
      apply tsum_congr
      intro pair
      apply ContinuousLinearMap.ext
      intro value
      rfl
    _ = ∑' pair : KernelShift × KernelShift,
          fullKernelTripleTerm first second third total input
            (fullKernelRightAssocEquiv total pair) :=
      ((fullKernelRightAssocEquiv total).tsum_eq
        (fullKernelTripleTerm first second third total input)).symm
    _ = ∑' pair : KernelShift × KernelShift,
        (first.entry (total - pair.1) (input + pair.1)).comp
          ((second.entry (pair.1 - pair.2) (input + pair.2)).comp
            (third.entry pair.2 input)) := by
      apply tsum_congr
      intro pair
      unfold fullKernelTripleTerm fullKernelRightAssocEquiv
      simp only [Equiv.coe_fn_mk]
      have outerInput :
          input + (total - (total - pair.1)) = input + pair.1 := by
        ext <;> dsimp <;> ring
      have innerShift :
          total - (total - pair.1) - (pair.1 - pair.2) = pair.2 := by
        ext <;> dsimp <;> ring
      rw [outerInput, innerShift]
      apply ContinuousLinearMap.ext
      intro value
      rfl
    _ = ∑' outer : KernelShift, ∑' middle : KernelShift,
        (first.entry (total - outer) (input + outer)).comp
          ((second.entry (outer - middle) (input + middle)).comp
            (third.entry middle input)) := rightPairSummable.tsum_prod
    _ = ∑' outer : KernelShift,
        (first.entry (total - outer) (input + outer)).comp
          (∑' middle : KernelShift,
            (second.entry (outer - middle) (input + middle)).comp
              (third.entry middle input)) := by
      apply tsum_congr
      intro outer
      let composeLeft := (ContinuousLinearMap.compL ℂ
        (ComplexEuclidean inputDimension) (ComplexEuclidean secondMiddleDimension)
          (ComplexEuclidean outputDimension))
        (first.entry (total - outer) (input + outer))
      change (∑' middle : KernelShift, composeLeft
          ((second.entry (outer - middle) (input + middle)).comp
            (third.entry middle input))) =
        composeLeft (∑' middle : KernelShift,
          (second.entry (outer - middle) (input + middle)).comp
            (third.entry middle input))
      exact (composeLeft.map_tsum
        (fullKernelCompositionTerm_summable second third outer input)).symm

end Grad.BoundaryKernelAction
