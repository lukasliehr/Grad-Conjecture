import ProductFiniteAllocations
import ProductFrequencyAllocation
import ProductWeightedCell

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def productAllocationConstant (arity grade order defect : ℕ) : ℝ :=
  (order.choose defect : ℝ) * productDefectDerivativeConstant arity defect *
    (arity : ℝ) ^ (grade - (order - defect)) * allocationMultiplicity arity (order - defect)

theorem productAllocationConstant_nonnegative (arity grade order defect : ℕ) :
    0 ≤ productAllocationConstant arity grade order defect :=
  mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (productDefectDerivativeConstant_nonnegative _ _)) (pow_nonneg (Nat.cast_nonneg _) _))
      (allocationMultiplicity_nonnegative _ _)

theorem weightedProduct_allocated_point_bound {arity outputDimension : ℕ}
    {dimensions : Fin arity → ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (grade order : ℕ) (orderBound : order ≤ grade) (point : ClosedDisk) :
    cellFrequency (∑ index, cells index) ^ (grade - order) *
      ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication fields) point.val‖ ≤
      ∑ defect ∈ Finset.range (order + 1), productAllocationConstant arity grade order defect *
        ‖multiplication‖ * ∑ allocation : BoundedAllocation arity (order - defect),
          ∑ chosen : Fin arity, cellFrequency (cells chosen) ^ (grade - (order - defect)) *
            ∏ index, ‖jetOperatorDerivative (allocation.val index).val
              (phaseWeightedJet parameters (cells index) (fields index)) point‖ := by
  let sizes : Fin arity → ℕ → ℝ := fun index rank =>
    ‖jetOperatorDerivative rank (phaseWeightedJet parameters (cells index) (fields index)) point‖
  have sizesNonnegative (index : Fin arity) (rank : ℕ) : 0 ≤ sizes index rank := norm_nonneg _
  apply (mul_le_mul_of_nonneg_left
    (weightedProductSmooth_derivative_bound positiveArity parameters cells multiplication fields order point)
    (pow_nonneg (cellFrequency_pos _).le _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro defect defectIn
  have defectBound : defect ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp defectIn)
  have frequencyBound := residual_frequency_bound positiveArity cells grade order defect (order - defect)
    orderBound (Nat.add_sub_of_le defectBound)
  have allocationBound := derivativeAllocation_le_finite_sum sizes sizesNonnegative (order - defect)
  have prefixNonnegative : 0 ≤ (order.choose defect : ℝ) *
      productDefectDerivativeConstant arity defect * ‖multiplication‖ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (productDefectDerivativeConstant_nonnegative _ _))
      (norm_nonneg _)
  change cellFrequency (∑ index, cells index) ^ (grade - order) *
    ((order.choose defect : ℝ) *
      (productDefectDerivativeConstant arity defect * productFrequency cells ^ defect) *
        (‖multiplication‖ * derivativeAllocation arity sizes (order - defect))) ≤ _
  calc
    _ = ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect * ‖multiplication‖) *
        ((cellFrequency (∑ index, cells index) ^ (grade - order) * productFrequency cells ^ defect) *
          derivativeAllocation arity sizes (order - defect)) := by ring
    _ ≤ ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect * ‖multiplication‖) *
        (((arity : ℝ) ^ (grade - (order - defect)) *
          ∑ chosen, cellFrequency (cells chosen) ^ (grade - (order - defect))) *
            (allocationMultiplicity arity (order - defect) *
              ∑ allocation : BoundedAllocation arity (order - defect),
                ∏ index, sizes index (allocation.val index).val)) := by
      apply mul_le_mul_of_nonneg_left _ prefixNonnegative
      exact mul_le_mul frequencyBound allocationBound
        (derivativeAllocation_nonnegative sizes sizesNonnegative _)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Finset.sum_nonneg
          (fun _ _ => pow_nonneg (cellFrequency_pos _).le _)))
    _ = _ := by
      simp only [productAllocationConstant, Finset.sum_mul, Finset.mul_sum, sizes]
      apply Finset.sum_congr rfl
      intro allocation _
      apply Finset.sum_congr rfl
      intro chosen _
      ring

end Grad.NonlinearProduct
