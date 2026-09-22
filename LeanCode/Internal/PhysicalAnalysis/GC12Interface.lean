import GC11Proof

noncomputable section

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann
open Grad.WeakTesting.Commutation

/-- The order-zero multi-index inside an arbitrary finite coefficient grade. -/
def zeroDerivativeIndexAt (grade : ℕ) : DerivativeIndex grade :=
  ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), by simp⟩

/-- A labelled derivative position in the canonical concatenation of the
first and second Cartesian directions. -/
abbrev DerivativeLabel {grade : ℕ} (index : DerivativeIndex grade) :=
  Fin ((index.1.1 : ℕ) + (index.1.2 : ℕ))

/-- The commuting Cartesian multi-index carried by a nonempty selected block
of the currently remaining labelled positions. -/
def selectedBlockDerivativeIndex {grade : ℕ} (index : DerivativeIndex grade)
    (selected : Finset (DerivativeLabel index)) : DerivativeIndex grade :=
  lowerDerivativeIndex index (selectionDerivativeSplit index selected)

/-- The derivative index on the ordered complement of a selected block. -/
def remainingDerivativeIndex {grade : ℕ} (index : DerivativeIndex grade)
    (selected : Finset (DerivativeLabel index)) : DerivativeIndex grade :=
  upperDerivativeIndex index (selectionDerivativeSplit index selected)

theorem selectedBlockDerivativeOrder {grade : ℕ} (index : DerivativeIndex grade)
    (selected : Finset (DerivativeLabel index)) :
    derivativeOrder (selectedBlockDerivativeIndex index selected) = selected.card := by
  let word := selectedCartesianSubword (derivativeMultiIndex index) selected
  let first := directionCount word 0
  let second := directionCount word 1
  have total : first + second = selected.card := by
    dsimp only [first, second]
    exact word_direction_count_total selected.card word
  unfold selectedBlockDerivativeIndex
  change ((selectionDerivativeSplit index selected).1 : ℕ) +
      ((selectionDerivativeSplit index selected).2 : ℕ) = selected.card
  unfold selectionDerivativeSplit
  change (Grad.OrderedMultiplicity.countZeros
        (selectionWordPairEquiv (derivativeMultiIndex index).1
          (derivativeMultiIndex index).2 selected).1).val +
      (Grad.OrderedMultiplicity.countZeros
        (selectionWordPairEquiv (derivativeMultiIndex index).1
          (derivativeMultiIndex index).2 selected).2).val = selected.card
  rw [← selectedCartesianSubword_zero_count (derivativeMultiIndex index) selected,
    ← selectedCartesianSubword_one_count (derivativeMultiIndex index) selected]
  exact total

theorem remainingDerivativeOrder_add_selectedCard {grade : ℕ}
    (index : DerivativeIndex grade) (selected : Finset (DerivativeLabel index)) :
    derivativeOrder (remainingDerivativeIndex index selected) + selected.card =
      derivativeOrder index := by
  have splitOrder := derivative_split_order index
    (selectionDerivativeSplit index selected)
  have selectedOrder := selectedBlockDerivativeOrder index selected
  unfold selectedBlockDerivativeIndex at selectedOrder
  unfold remainingDerivativeIndex
  omega

theorem remainingDerivativeOrder_lt {grade : ℕ}
    (index : DerivativeIndex grade) (selected : Finset (DerivativeLabel index))
    (nonempty : selected.Nonempty) :
    derivativeOrder (remainingDerivativeIndex index selected) < derivativeOrder index := by
  have positive : 0 < selected.card := Finset.card_pos.mpr nonempty
  have total := remainingDerivativeOrder_add_selectedCard index selected
  omega

/-- An ordered partition of every labelled derivative position into nonempty
blocks.  Surjectivity is exactly the nonemptiness condition on each block. -/
structure OrderedDerivativePartition {grade : ℕ}
    (index : DerivativeIndex grade) where
  blockCount : Fin (derivativeOrder index + 1)
  blockOf : DerivativeLabel index → Fin blockCount
  nonemptyBlock : Function.Surjective blockOf
deriving Fintype

/-- The commuting Cartesian multi-index carried by one labelled block. -/
def partitionBlockDerivativeIndex {grade : ℕ} {index : DerivativeIndex grade}
    (partition : OrderedDerivativePartition index)
    (block : Fin partition.blockCount) : DerivativeIndex grade :=
  selectedBlockDerivativeIndex index
    (Finset.univ.filter fun position : DerivativeLabel index =>
      partition.blockOf position = block)

/-- Literal cell fields, used to state the noncommutative ordered-partition
formula without hiding any convolution or pointwise realization. -/
abbrev CellField (dimension : ℕ) :=
  ℤ → ClosedDisk → OperatorValue dimension dimension

def cellFieldComposition {dimension : ℕ}
    (outer inner : CellField dimension) : CellField dimension :=
  fun cell point => ∑' first : ℤ,
    (outer first point).comp (inner (cell - first) point)

def baseCellField {L sigma gamma ell : ℝ} {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    CellField dimension :=
  fun cell point => coefficientValue coefficient cell point

def gradedDerivativeCellField {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) : CellField dimension :=
  fun cell point => coefficientDerivative coefficient cell index point

/-- One term `G (δ^I¹ H) G ⋯ (δ^Iʲ H) G`, in the exact block order of a
labelled ordered partition.  The unique empty partition has term `G`. -/
def inversePartitionTerm {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    (inverse : BaseCoefficient L sigma gamma ell dimension)
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    {index : DerivativeIndex grade}
    (partition : OrderedDerivativePartition index) : CellField dimension :=
  let factors := (List.ofFn fun block : Fin partition.blockCount =>
    [gradedDerivativeCellField coefficient
        (partitionBlockDerivativeIndex partition block),
      baseCellField inverse]).flatten
  factors.foldl cellFieldComposition (baseCellField inverse)

/-- The finite ordered sum over all labelled ordered partitions, expanded by
the first nonempty block.  At order zero the unique empty partition contributes
`G`; at positive order the recursion is the standard first-block/tail
enumeration of the finite ordered partitions above. -/
def inverseDerivativePartitionSum {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (inverse : BaseCoefficient L sigma gamma ell dimension)
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) : CellField dimension :=
  WellFounded.fix (measure derivativeOrder).wf
    (C := fun _index => CellField dimension)
    (fun current recurse => by
      classical
      by_cases zero : derivativeOrder current = 0
      · exact baseCellField inverse
      · exact ∑ selected :
            {block : Finset (DerivativeLabel current) // block.Nonempty},
          cellFieldComposition (baseCellField inverse)
            (cellFieldComposition
              (gradedDerivativeCellField coefficient
                (selectedBlockDerivativeIndex current selected.1))
              (recurse (remainingDerivativeIndex current selected.1)
                (remainingDerivativeOrder_lt current selected.1 selected.2))))
    index

/-- A grade-`q` coefficient and a base coefficient realize the same literal
cell field on the original closed disk. -/
def RealizesSameCoefficient {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    (base : BaseCoefficient L sigma gamma ell dimension)
    (graded : Coefficient L sigma gamma ell grade dimension dimension) : Prop :=
  ∀ (cell : ℤ) (point : ClosedDisk),
    coefficientDerivative graded cell (zeroDerivativeIndexAt grade) point =
      coefficientValue base cell point

/-- Exact AP13 witness: the base inverse constructed by CT_GC11 has one
representative in the original grade, and every positive derivative is the
literal ordered-partition formula. -/
structure AllGradeInverseWitness {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ) where
  inverse : Coefficient L sigma gamma ell grade dimension dimension
  same_base_inverse : RealizesSameCoefficient
    (analyticCapCoefficientNeumannInverse admissible baseCoefficient) inverse
  positive_derivative : ∀ (index : DerivativeIndex grade),
    0 < derivativeOrder index → ∀ (cell : ℤ) (point : ClosedDisk),
      coefficientDerivative inverse cell index point =
        inverseDerivativePartitionSum
          (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
          gradedCoefficient index cell point

def BlockGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ) (admissible : Admissible L sigma gamma ell)
    (grade dimension : ℕ), 0 < dimension →
    ∀ (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
      (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
      (theta : ℝ),
      RealizesSameCoefficient baseCoefficient gradedCoefficient →
      ‖baseCoefficient‖ ≤ theta → theta < 1 →
        Nonempty (AllGradeInverseWitness admissible baseCoefficient
          gradedCoefficient theta)

end Grad.GaugeCoefficients.Neumann.Regularity
