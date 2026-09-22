import GC12CellInverse

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

theorem CellFieldSummable.zero (dimension : ℕ) :
    CellFieldSummable (0 : CellField dimension) := by
  intro point
  simp

theorem CellFieldSummable.fintype_sum {dimension : ℕ} {Index : Type*}
    [Fintype Index] [DecidableEq Index] {fields : Index → CellField dimension}
    (summable : ∀ index, CellFieldSummable (fields index)) :
    CellFieldSummable (∑ index, fields index) := by
  let all : Finset Index := Finset.univ
  change CellFieldSummable (∑ index ∈ all, fields index)
  induction all using Finset.induction_on with
  | empty => simpa using CellFieldSummable.zero dimension
  | @insert index remaining notMember inductionHypothesis =>
      rw [Finset.sum_insert notMember]
      exact (summable index).add inductionHypothesis

theorem coefficientDerivative_add {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (first second : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (first + second) cell index point =
      coefficientDerivative first cell index point +
        coefficientDerivative second cell index point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (first.1 (cell, index) point + second.1 (cell, index) point) =
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
        first.1 (cell, index) point +
      ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
        second.1 (cell, index) point
  exact smul_add _ _ _

def zeroDerivativeSplitAtIndex {grade : ℕ} (index : DerivativeIndex grade) :
    DerivativeSplit index :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

@[simp] theorem lowerDerivativeIndex_zeroSplitAtIndex {grade : ℕ}
    (index : DerivativeIndex grade) :
    lowerDerivativeIndex index (zeroDerivativeSplitAtIndex index) =
      zeroDerivativeIndexAt grade := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem upperDerivativeIndex_zeroSplitAtIndex {grade : ℕ}
    (index : DerivativeIndex grade) :
    upperDerivativeIndex index (zeroDerivativeSplitAtIndex index) = index := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;>
    simp [upperDerivativeIndex, zeroDerivativeSplitAtIndex]

@[simp] theorem splitMultiplicity_zeroSplitAtIndex {grade : ℕ}
    (index : DerivativeIndex grade) :
    splitMultiplicity index (zeroDerivativeSplitAtIndex index) = 1 := by
  simp [splitMultiplicity, zeroDerivativeSplitAtIndex]

theorem split_ne_zero_of_lower_order_positive {grade : ℕ}
    {index : DerivativeIndex grade} {split : DerivativeSplit index}
    (positive : 0 < derivativeOrder (lowerDerivativeIndex index split)) :
    split ≠ zeroDerivativeSplitAtIndex index := by
  intro same
  subst split
  simp only [lowerDerivativeIndex_zeroSplitAtIndex, derivativeOrder,
    zeroDerivativeIndexAt, add_zero] at positive
  omega

theorem lower_order_positive_of_split_ne_zero {grade : ℕ}
    {index : DerivativeIndex grade} {split : DerivativeSplit index}
    (different : split ≠ zeroDerivativeSplitAtIndex index) :
    0 < derivativeOrder (lowerDerivativeIndex index split) := by
  by_contra notPositive
  have orderZero : derivativeOrder (lowerDerivativeIndex index split) = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  have firstZero : (split.1 : ℕ) = 0 := by
    simp only [derivativeOrder, lowerDerivativeIndex] at orderZero
    omega
  have secondZero : (split.2 : ℕ) = 0 := by
    simp only [derivativeOrder, lowerDerivativeIndex] at orderZero
    omega
  apply different
  apply Prod.ext <;> apply Fin.ext
  · exact firstZero
  · exact secondZero

def derivativeSplitCellTerm {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    CellField dimension :=
  (splitMultiplicity index split : ℂ) •
    cellFieldComposition
      (gradedDerivativeCellField coefficient (lowerDerivativeIndex index split))
      (gradedDerivativeCellField inverse (upperDerivativeIndex index split))

theorem derivativeSplitCellTerm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    CellFieldSummable (derivativeSplitCellTerm coefficient inverse index split) :=
  ((gradedDerivativeCellField_summable admissible coefficient _).composition
    (gradedDerivativeCellField_summable admissible inverse _)).smul _

theorem formalCompositionDerivative_eq_splitCellSum {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    formalCompositionDerivative coefficient inverse cell index point =
      (∑ split : DerivativeSplit index,
        derivativeSplitCellTerm coefficient inverse index split) cell point := by
  unfold formalCompositionDerivative
  rw [Summable.tsum_finsetSum (fun split _membership =>
    formalCompositionSplit_summable admissible grade coefficient inverse
      cell index split point)]
  let evaluation : CellField dimension →+
      OperatorValue dimension dimension := {
    toFun := fun field => field cell point
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  change (∑ split : DerivativeSplit index, ∑' first : ℤ,
      (splitMultiplicity index split : ℂ) •
        (coefficientDerivative coefficient first
          (lowerDerivativeIndex index split) point).comp
        (coefficientDerivative inverse (cell - first)
          (upperDerivativeIndex index split) point)) = evaluation
    (∑ split : DerivativeSplit index,
      derivativeSplitCellTerm coefficient inverse index split)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  unfold derivativeSplitCellTerm cellFieldComposition
  change (∑' first : ℤ,
      (splitMultiplicity index split : ℂ) •
        (coefficientDerivative coefficient first
          (lowerDerivativeIndex index split) point).comp
        (coefficientDerivative inverse (cell - first)
          (upperDerivativeIndex index split) point)) =
    (splitMultiplicity index split : ℂ) •
      ∑' first : ℤ,
        (coefficientDerivative coefficient first
          (lowerDerivativeIndex index split) point).comp
        (coefficientDerivative inverse (cell - first)
          (upperDerivativeIndex index split) point)
  exact Summable.tsum_const_smul (splitMultiplicity index split : ℂ)
    (cellFieldComposition_fixed_summable
      (gradedDerivativeCellField_summable admissible coefficient _)
      (gradedDerivativeCellField_summable admissible inverse _) cell point)

def positiveDerivativeSplitForcing {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) : CellField dimension :=
  ∑ split : DerivativeSplit index,
    if split = zeroDerivativeSplitAtIndex index then 0 else
      derivativeSplitCellTerm coefficient inverse index split

theorem positiveDerivativeSplitForcing_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) :
    CellFieldSummable
      (positiveDerivativeSplitForcing coefficient inverse index) := by
  unfold positiveDerivativeSplitForcing
  apply CellFieldSummable.fintype_sum
  intro split
  by_cases same : split = zeroDerivativeSplitAtIndex index
  · simp [same]
    exact CellFieldSummable.zero dimension
  · simp only [same, ↓reduceIte]
    exact derivativeSplitCellTerm_summable admissible coefficient inverse index split

theorem derivativeSplitSum_eq_zero_add_forcing {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (coefficient inverse : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) :
    (∑ split : DerivativeSplit index,
      derivativeSplitCellTerm coefficient inverse index split) =
    derivativeSplitCellTerm coefficient inverse index
        (zeroDerivativeSplitAtIndex index) +
      positiveDerivativeSplitForcing coefficient inverse index := by
  unfold positiveDerivativeSplitForcing
  let term := derivativeSplitCellTerm coefficient inverse index
  change (∑ split, term split) = term (zeroDerivativeSplitAtIndex index) +
    ∑ split, if split = zeroDerivativeSplitAtIndex index then 0 else term split
  calc
    (∑ split, term split) =
        ∑ split,
          ((if split = zeroDerivativeSplitAtIndex index then term split else 0) +
            if split = zeroDerivativeSplitAtIndex index then 0 else term split) := by
      apply Finset.sum_congr rfl
      intro split _membership
      by_cases same : split = zeroDerivativeSplitAtIndex index <;> simp [same]
    _ = (∑ split,
          if split = zeroDerivativeSplitAtIndex index then term split else 0) +
        ∑ split,
          if split = zeroDerivativeSplitAtIndex index then 0 else term split :=
      Finset.sum_add_distrib
    _ = _ := by simp

theorem derivativeSplitCellTerm_zero {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    {baseCoefficient : BaseCoefficient L sigma gamma ell dimension}
    (gradedCoefficient inverse :
      Coefficient L sigma gamma ell grade dimension dimension)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (index : DerivativeIndex grade) :
    derivativeSplitCellTerm gradedCoefficient inverse index
        (zeroDerivativeSplitAtIndex index) =
      cellFieldComposition (baseCellField baseCoefficient)
        (gradedDerivativeCellField inverse index) := by
  unfold derivativeSplitCellTerm
  simp only [splitMultiplicity_zeroSplitAtIndex, Nat.cast_one, one_smul,
    lowerDerivativeIndex_zeroSplitAtIndex, upperDerivativeIndex_zeroSplitAtIndex]
  congr 1
  funext cell point
  exact realizes cell point

theorem inverseDerivative_fixedPoint {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positiveDimension : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1)
    (index : DerivativeIndex grade) (positiveOrder : 0 < derivativeOrder index) :
    gradedDerivativeCellField
        (gradedCoefficientNeumannInverse admissible gradedCoefficient) index =
      cellFieldComposition (baseCellField baseCoefficient)
        (gradedDerivativeCellField
          (gradedCoefficientNeumannInverse admissible gradedCoefficient) index) +
      positiveDerivativeSplitForcing gradedCoefficient
        (gradedCoefficientNeumannInverse admissible gradedCoefficient) index := by
  let inverse := gradedCoefficientNeumannInverse admissible gradedCoefficient
  have fixedPoint := gradedCoefficientNeumannInverse_fixedPoint admissible
    positiveDimension baseCoefficient gradedCoefficient theta realizes normBound thetaLt
  funext cell point
  have derivativeEquality := congrArg
    (fun coefficient : Coefficient L sigma gamma ell grade dimension dimension =>
      coefficientDerivative coefficient cell index point) fixedPoint
  rw [coefficientDerivative_add,
    gradedIdentityCoefficient_positiveDerivative L sigma gamma ell grade dimension
      cell index positiveOrder point,
    coefficientComposition_derivative] at derivativeEquality
  simp only [zero_add] at derivativeEquality
  rw [formalCompositionDerivative_eq_splitCellSum admissible] at derivativeEquality
  rw [derivativeSplitSum_eq_zero_add_forcing] at derivativeEquality
  rw [derivativeSplitCellTerm_zero gradedCoefficient inverse realizes] at derivativeEquality
  exact derivativeEquality

theorem inverseDerivative_recurrence {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positiveDimension : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1)
    (index : DerivativeIndex grade) (positiveOrder : 0 < derivativeOrder index) :
    gradedDerivativeCellField
        (gradedCoefficientNeumannInverse admissible gradedCoefficient) index =
      cellFieldComposition
        (baseCellField (analyticCapCoefficientNeumannInverse admissible baseCoefficient))
        (positiveDerivativeSplitForcing gradedCoefficient
          (gradedCoefficientNeumannInverse admissible gradedCoefficient) index) := by
  let inverse := gradedCoefficientNeumannInverse admissible gradedCoefficient
  let baseInverse := analyticCapCoefficientNeumannInverse admissible baseCoefficient
  apply cellField_fixedPoint_solution
    (inverseSummable := baseCellField_summable admissible baseInverse)
    (coefficientSummable := baseCellField_summable admissible baseCoefficient)
    (unknownSummable := gradedDerivativeCellField_summable admissible inverse index)
    (_forcingSummable := positiveDerivativeSplitForcing_summable admissible
      gradedCoefficient inverse index)
  · exact analyticCapInverseCellField_rightInverse admissible positiveDimension
      baseCoefficient theta normBound thetaLt
  · exact inverseDerivative_fixedPoint admissible positiveDimension baseCoefficient
      gradedCoefficient theta realizes normBound thetaLt index positiveOrder

end Grad.GaugeCoefficients.Neumann.Regularity
