import ProductPointAllocations

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

abbrev ProductAllocationIndex (arity order : ℕ) :=
  (defect : Fin (order + 1)) × (BoundedAllocation arity (order - defect.val) × Fin arity)

def allocationOrder {arity order : ℕ} (choice : ProductAllocationIndex arity order) (index : Fin arity) : ℕ :=
  (choice.2.1.val index).val

def allocationPower {arity order : ℕ} (grade : ℕ)
    (choice : ProductAllocationIndex arity order) (index : Fin arity) : ℕ :=
  if index = choice.2.2 then grade - (order - choice.1.val) else 0

theorem allocationOrderPower_total {arity order : ℕ} (grade : ℕ)
    (choice : ProductAllocationIndex arity order) (orderBound : order ≤ grade) :
    (∑ index : Fin arity, (allocationOrder (arity := arity) (order := order) choice index +
      allocationPower (arity := arity) (order := order) grade choice index)) = grade := by
  exact frequencyAssignedOrders_total grade choice.2.1 choice.2.2
    ((Nat.sub_le _ _).trans orderBound)

theorem allocated_frequency_product {arity order : ℕ} (grade : ℕ)
    (choice : ProductAllocationIndex arity order) (cells : Fin arity → ℤ) :
    (∏ index, cellFrequency (cells index) ^ allocationPower grade choice index) =
      cellFrequency (cells choice.2.2) ^ (grade - (order - choice.1.val)) := by
  classical
  simp only [allocationPower, apply_ite, pow_zero]
  simp

theorem allocated_finite_sum {arity order : ℕ} (grade : ℕ) (cells : Fin arity → ℤ)
    (sizes : Fin arity → ℕ → ℝ) (coefficients : ℕ → ℝ) :
    (∑ choice : ProductAllocationIndex arity order, coefficients choice.1.val *
      ∏ index, cellFrequency (cells index) ^ allocationPower grade choice index *
        sizes index (allocationOrder choice index)) =
    ∑ defect ∈ Finset.range (order + 1), coefficients defect *
      ∑ allocation : BoundedAllocation arity (order - defect),
        ∑ chosen : Fin arity, cellFrequency (cells chosen) ^ (grade - (order - defect)) *
          ∏ index, sizes index (allocation.val index).val := by
  classical
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, defect, 2, allocation, 2, chosen]
    rw [Finset.prod_mul_distrib, allocated_frequency_product]
  simp only [allocationOrder]
  simp_rw [← Finset.mul_sum]
  exact Fin.sum_univ_eq_sum_range
    (fun defect => coefficients defect *
      ∑ allocation : BoundedAllocation arity (order - defect),
        ∑ chosen : Fin arity, cellFrequency (cells chosen) ^ (grade - (order - defect)) *
          ∏ index, sizes index (allocation.val index).val) (order + 1)

theorem weightedProduct_finite_point_bound {arity outputDimension : ℕ}
    {dimensions : Fin arity → ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (grade order : ℕ) (orderBound : order ≤ grade) (point : ClosedDisk) :
    cellFrequency (∑ index, cells index) ^ (grade - order) *
      ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication fields) point.val‖ ≤
      ∑ choice : ProductAllocationIndex arity order,
        productAllocationConstant arity grade order choice.1.val * ‖multiplication‖ *
          ∏ index, cellFrequency (cells index) ^ allocationPower grade choice index *
            ‖jetOperatorDerivative (allocationOrder choice index)
              (phaseWeightedJet parameters (cells index) (fields index)) point‖ := by
  classical
  apply (weightedProduct_allocated_point_bound positiveArity parameters cells multiplication fields
    grade order orderBound point).trans_eq
  exact (allocated_finite_sum grade cells
    (fun index rank => ‖jetOperatorDerivative rank (phaseWeightedJet parameters (cells index) (fields index)) point‖)
    (fun defect => productAllocationConstant arity grade order defect * ‖multiplication‖)).symm

end Grad.NonlinearProduct
