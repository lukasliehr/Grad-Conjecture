import GC12DerivativeRecurrence

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

theorem cellFieldComposition_add_inner {dimension : ℕ}
    {outer first second : CellField dimension}
    (outerSummable : CellFieldSummable outer)
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second) :
    cellFieldComposition outer (first + second) =
      cellFieldComposition outer first + cellFieldComposition outer second := by
  funext cell point
  unfold cellFieldComposition
  simp only [Pi.add_apply, ContinuousLinearMap.comp_add]
  exact (cellFieldComposition_fixed_summable outerSummable firstSummable cell point).tsum_add
    (cellFieldComposition_fixed_summable outerSummable secondSummable cell point)

theorem CellFieldSummable.finset_sum {dimension : ℕ} {Index : Type*}
    [DecidableEq Index]
    {fields : Index → CellField dimension} (indices : Finset Index)
    (summable : ∀ index ∈ indices, CellFieldSummable (fields index)) :
    CellFieldSummable (∑ index ∈ indices, fields index) := by
  induction indices using Finset.induction_on with
  | empty => simpa using CellFieldSummable.zero dimension
  | @insert index remaining notMember inductionHypothesis =>
      rw [Finset.sum_insert notMember]
      exact (summable index (by simp)).add
        (inductionHypothesis fun member membership =>
          summable member (by simp [membership]))

theorem cellFieldComposition_fintype_sum_inner {dimension : ℕ}
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    {outer : CellField dimension} {fields : Index → CellField dimension}
    (outerSummable : CellFieldSummable outer)
    (fieldsSummable : ∀ index, CellFieldSummable (fields index)) :
    cellFieldComposition outer (∑ index, fields index) =
      ∑ index, cellFieldComposition outer (fields index) := by
  let all : Finset Index := Finset.univ
  change cellFieldComposition outer (∑ index ∈ all, fields index) =
    ∑ index ∈ all, cellFieldComposition outer (fields index)
  induction all using Finset.induction_on with
  | empty =>
      funext cell point
      unfold cellFieldComposition
      simp
  | @insert index remaining notMember inductionHypothesis =>
      have remainingSummable :
          CellFieldSummable (∑ member ∈ remaining, fields member) :=
        CellFieldSummable.finset_sum remaining
          (fun member _membership => fieldsSummable member)
      rw [Finset.sum_insert notMember, Finset.sum_insert notMember,
        cellFieldComposition_add_inner outerSummable (fieldsSummable index)
          remainingSummable, inductionHypothesis]

theorem selectionDerivativeSplit_eq_zero_iff_not_nonempty {grade : ℕ}
    (index : DerivativeIndex grade) (selected : Finset (DerivativeLabel index)) :
    selectionDerivativeSplit index selected = zeroDerivativeSplitAtIndex index ↔
      ¬ selected.Nonempty := by
  constructor
  · intro same nonempty
    have selectedOrder := selectedBlockDerivativeOrder index selected
    unfold selectedBlockDerivativeIndex at selectedOrder
    have positive : 0 < derivativeOrder
        (lowerDerivativeIndex index (selectionDerivativeSplit index selected)) := by
      rw [selectedOrder]
      exact Finset.card_pos.mpr nonempty
    exact split_ne_zero_of_lower_order_positive positive same
  · intro empty
    by_contra different
    have positive := lower_order_positive_of_split_ne_zero different
    have cardPositive : 0 < selected.card := by
      have selectedOrder := selectedBlockDerivativeOrder index selected
      unfold selectedBlockDerivativeIndex at selectedOrder
      rw [← selectedOrder]
      exact positive
    exact empty (Finset.card_pos.mp cardPositive)

def selectedDerivativeCellTerm {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) (selected : Finset (DerivativeLabel index)) :
    CellField dimension :=
  cellFieldComposition
    (gradedDerivativeCellField coefficient
      (selectedBlockDerivativeIndex index selected))
    (gradedDerivativeCellField inverse
      (remainingDerivativeIndex index selected))

theorem positiveDerivativeSplitForcing_eq_selectedSum {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) :
    positiveDerivativeSplitForcing coefficient inverse index =
      ∑ selected : {block : Finset (DerivativeLabel index) // block.Nonempty},
        selectedDerivativeCellTerm coefficient inverse index selected.1 := by
  let family : DerivativeSplit index → CellField dimension := fun split =>
    if split = zeroDerivativeSplitAtIndex index then 0 else
      cellFieldComposition
        (gradedDerivativeCellField coefficient (lowerDerivativeIndex index split))
        (gradedDerivativeCellField inverse (upperDerivativeIndex index split))
  have grouped := sum_selectionDerivativeSplit index family
  have left :
      (∑ selected : Finset (DerivativeLabel index),
        family (selectionDerivativeSplit index selected)) =
      ∑ selected : {block : Finset (DerivativeLabel index) // block.Nonempty},
        selectedDerivativeCellTerm coefficient inverse index selected.1 := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter Finset.Nonempty)
      (fun selected => by simp) (fun selected =>
        selectedDerivativeCellTerm coefficient inverse index selected)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro selected _membership
    by_cases nonempty : selected.Nonempty
    · have different : selectionDerivativeSplit index selected ≠
          zeroDerivativeSplitAtIndex index :=
        fun same => (selectionDerivativeSplit_eq_zero_iff_not_nonempty
          index selected).mp same nonempty
      simp only [nonempty, ↓reduceIte, family, different]
      rfl
    · have same : selectionDerivativeSplit index selected =
          zeroDerivativeSplitAtIndex index :=
        (selectionDerivativeSplit_eq_zero_iff_not_nonempty index selected).mpr nonempty
      simp only [nonempty, ↓reduceIte, family, same]
  calc
    positiveDerivativeSplitForcing coefficient inverse index =
        ∑ split : DerivativeSplit index,
          splitMultiplicity index split • family split := by
      unfold positiveDerivativeSplitForcing derivativeSplitCellTerm
      apply Finset.sum_congr rfl
      intro split _membership
      by_cases same : split = zeroDerivativeSplitAtIndex index
      · simp [same, family]
      · simp only [same, ↓reduceIte, family]
        exact Nat.cast_smul_eq_nsmul ℂ (splitMultiplicity index split)
          (cellFieldComposition
            (gradedDerivativeCellField coefficient (lowerDerivativeIndex index split))
            (gradedDerivativeCellField inverse (upperDerivativeIndex index split)))
    _ = ∑ selected : Finset (Fin
          (cartesianOrder (derivativeMultiIndex index))),
          family (selectionDerivativeSplit index selected) := grouped.symm
    _ = ∑ selected : {block : Finset (DerivativeLabel index) // block.Nonempty},
          selectedDerivativeCellTerm coefficient inverse index selected.1 := left

theorem inverseDerivativePartitionSum_positive_unfold {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (inverse : BaseCoefficient L sigma gamma ell dimension)
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) (positive : 0 < derivativeOrder index) :
    inverseDerivativePartitionSum inverse coefficient index =
      ∑ selected : {block : Finset (DerivativeLabel index) // block.Nonempty},
        cellFieldComposition (baseCellField inverse)
          (cellFieldComposition
            (gradedDerivativeCellField coefficient
              (selectedBlockDerivativeIndex index selected.1))
            (inverseDerivativePartitionSum inverse coefficient
              (remainingDerivativeIndex index selected.1))) := by
  rw [inverseDerivativePartitionSum, WellFounded.fix_eq,
    dif_neg (Nat.ne_of_gt positive)]
  apply Finset.sum_congr rfl
  intro selected _membership
  rfl

end Grad.GaugeCoefficients.Neumann.Regularity
