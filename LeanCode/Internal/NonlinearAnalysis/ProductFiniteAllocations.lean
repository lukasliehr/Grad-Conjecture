import ProductDerivativeAllocation
import OriginalOneHighAllocation

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

abbrev BoundedAllocation (arity order : ℕ) :=
  {orders : Fin arity → Fin (order + 1) // ∑ index, (orders index).val = order}

theorem derivativeAllocation_le_finite_sum {arity : ℕ}
    (sizes : Fin arity → ℕ → ℝ) (nonnegative : ∀ index order, 0 ≤ sizes index order) (order : ℕ) :
    derivativeAllocation arity sizes order ≤ allocationMultiplicity arity order *
      ∑ allocation : BoundedAllocation arity order, ∏ index, sizes index (allocation.val index).val := by
  have bound := derivativeAllocation_le_of_allocation_bound sizes nonnegative order 1
    (∑ allocation : BoundedAllocation arity order, ∏ index, sizes index (allocation.val index).val)
    zero_le_one
  rw [one_mul] at bound
  apply bound
  intro orders total
  have eachBound (index : Fin arity) : orders index ≤ order := by
    rw [← total]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  let allocation : BoundedAllocation arity order :=
    ⟨fun index => ⟨orders index, Nat.lt_succ_of_le (eachBound index)⟩, total⟩
  simpa only [one_mul] using Finset.single_le_sum
    (f := fun choice : BoundedAllocation arity order => ∏ index, sizes index (choice.val index).val)
    (fun _ _ => Finset.prod_nonneg (fun index _ => nonnegative index _)) (Finset.mem_univ allocation)

def frequencyAssignedOrders {arity order : ℕ} (grade : ℕ)
    (allocation : BoundedAllocation arity order) (chosen : Fin arity) (index : Fin arity) : ℕ :=
  (allocation.val index).val + if index = chosen then grade - order else 0

theorem frequencyAssignedOrders_total {arity order : ℕ} (grade : ℕ)
    (allocation : BoundedAllocation arity order) (chosen : Fin arity) (orderBound : order ≤ grade) :
    (∑ index, frequencyAssignedOrders grade allocation chosen index) = grade := by
  simp only [frequencyAssignedOrders, Finset.sum_add_distrib, allocation.property]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  omega

theorem frequencyAssignedOrders_one_high {arity order grade : ℕ} (gradePositive : 0 < grade)
    (allocation : BoundedAllocation arity order) (chosen : Fin arity) (orderBound : order ≤ grade)
    {dimensions : Fin arity → ℕ} {parameters : Grad.CartesianState.PhaseParameters}
    (fields : (index : Fin arity) → Grad.CartesianState.ACore parameters (dimensions index)) :
    (∏ index, originalGradeNorm (frequencyAssignedOrders grade allocation chosen index + 3) (fields index)) ≤
      allocationInterpolationConstant grade ^ arity *
        ∑ index, originalGradeNorm (grade + 3) (fields index) *
          ∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other) :=
  original_allocated_product_one_high grade gradePositive (frequencyAssignedOrders grade allocation chosen)
    (frequencyAssignedOrders_total grade allocation chosen orderBound) fields

end Grad.NonlinearProduct
