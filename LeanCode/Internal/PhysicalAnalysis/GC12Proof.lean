import GC12Partitions

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

theorem derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero {grade : ℕ}
    (index : DerivativeIndex grade) (zero : derivativeOrder index = 0) :
    index = zeroDerivativeIndexAt grade := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals simp only [derivativeOrder] at zero
  all_goals simp only [zeroDerivativeIndexAt]
  all_goals omega

theorem inverseDerivativePartitionSum_zero {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (inverse : BaseCoefficient L sigma gamma ell dimension)
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) (zero : derivativeOrder index = 0) :
    inverseDerivativePartitionSum inverse coefficient index =
      baseCellField inverse := by
  rw [inverseDerivativePartitionSum, WellFounded.fix_eq, dif_pos zero]

theorem gradedCoefficientNeumannInverse_partitionFormula
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positiveDimension : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1)
    (index : DerivativeIndex grade) :
    gradedDerivativeCellField
        (gradedCoefficientNeumannInverse admissible gradedCoefficient) index =
      inverseDerivativePartitionSum
        (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
        gradedCoefficient index := by
  by_cases zero : derivativeOrder index = 0
  · have indexZero := derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero index zero
    subst index
    rw [inverseDerivativePartitionSum_zero _ _ _
      (by simp [derivativeOrder, zeroDerivativeIndexAt])]
    funext cell point
    exact gradedCoefficientNeumannInverse_realizes admissible positiveDimension
      baseCoefficient gradedCoefficient theta realizes normBound thetaLt cell point
  · have positiveOrder : 0 < derivativeOrder index := Nat.pos_of_ne_zero zero
    rw [inverseDerivative_recurrence admissible positiveDimension baseCoefficient
      gradedCoefficient theta realizes normBound thetaLt index positiveOrder]
    rw [positiveDerivativeSplitForcing_eq_selectedSum]
    rw [inverseDerivativePartitionSum_positive_unfold
      (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
      gradedCoefficient index positiveOrder]
    have inverseSummable := baseCellField_summable admissible
      (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
    have selectedSummable : ∀ selected :
        {block : Finset (DerivativeLabel index) // block.Nonempty},
        CellFieldSummable (selectedDerivativeCellTerm gradedCoefficient
          (gradedCoefficientNeumannInverse admissible gradedCoefficient)
          index selected.1) := fun selected =>
      (gradedDerivativeCellField_summable admissible gradedCoefficient
        (selectedBlockDerivativeIndex index selected.1)).composition
      (gradedDerivativeCellField_summable admissible
        (gradedCoefficientNeumannInverse admissible gradedCoefficient)
        (remainingDerivativeIndex index selected.1))
    rw [cellFieldComposition_fintype_sum_inner inverseSummable selectedSummable]
    apply Finset.sum_congr rfl
    intro selected _membership
    unfold selectedDerivativeCellTerm
    rw [gradedCoefficientNeumannInverse_partitionFormula admissible
      positiveDimension baseCoefficient gradedCoefficient theta realizes normBound
      thetaLt (remainingDerivativeIndex index selected.1)]
termination_by derivativeOrder index
decreasing_by
  exact remainingDerivativeOrder_lt index selected.1 selected.2

/-- CT_GC12 / AP13: the base Neumann inverse has an all-grade representative,
and every positive derivative is the literal finite ordered-labelled-partition
formula. -/
theorem blockGoal : BlockGoal := by
  intro L sigma gamma ell admissible grade dimension positiveDimension
    baseCoefficient gradedCoefficient theta realizes normBound thetaLt
  exact ⟨{
    inverse := gradedCoefficientNeumannInverse admissible gradedCoefficient
    same_base_inverse := gradedCoefficientNeumannInverse_realizes admissible
      positiveDimension baseCoefficient gradedCoefficient theta realizes normBound thetaLt
    positive_derivative := by
      intro index positiveOrder cell point
      exact congrFun (congrFun
        (gradedCoefficientNeumannInverse_partitionFormula admissible
          positiveDimension baseCoefficient gradedCoefficient theta realizes normBound
          thetaLt index) cell) point
  }⟩

end Grad.GaugeCoefficients.Neumann.Regularity
