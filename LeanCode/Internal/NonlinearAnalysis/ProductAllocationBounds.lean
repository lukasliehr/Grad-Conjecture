import ProductAllocatedConvolution
import ProductZeroGradeAllocation

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.CartesianState

def allocatedNormProduct {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ} {parameters : PhaseParameters}
    (orders : Fin (arity + 1) → ℕ)
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) : ℝ :=
  (∏ index : Fin arity, originalGradeNorm (orders index.castSucc + 3) (fields index.castSucc)) *
    originalGradeNorm (orders (Fin.last arity)) (fields (Fin.last arity))

theorem allocatedNormProduct_nonnegative {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    {parameters : PhaseParameters} (orders : Fin (arity + 1) → ℕ)
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) :
    0 ≤ allocatedNormProduct orders fields :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _)) (originalGradeNorm_nonnegative _ _)

theorem allocatedNormProduct_le_all_shifted {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    {parameters : PhaseParameters} (orders : Fin (arity + 1) → ℕ)
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) :
    allocatedNormProduct orders fields ≤ ∏ index, originalGradeNorm (orders index + 3) (fields index) := by
  rw [Fin.prod_univ_castSucc]
  exact mul_le_mul_of_nonneg_left (cartesianGrade_norm_mono parameters (Nat.le_add_right _ 3) _)
    (Finset.prod_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _))

def allocatedGradeExpression {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) : ℝ :=
  ∑ allocation : BoundedAllocation (arity + 1) grade,
    allocatedNormProduct (fun index => (allocation.val index).val) fields

theorem boundedAllocation_single_le {arity grade : ℕ}
    (value : (Fin arity → ℕ) → ℝ) (nonnegative : ∀ orders, 0 ≤ value orders)
    (orders : Fin arity → ℕ) (total : ∑ index, orders index = grade) :
    value orders ≤ ∑ allocation : BoundedAllocation arity grade,
      value (fun index => (allocation.val index).val) := by
  have eachBound (index : Fin arity) : orders index ≤ grade := by
    rw [← total]
    exact Finset.single_le_sum (f := orders) (s := Finset.univ)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  let allocation : BoundedAllocation arity grade :=
    ⟨fun index => ⟨orders index, Nat.lt_succ_of_le (eachBound index)⟩, total⟩
  exact Finset.single_le_sum
    (f := fun choice : BoundedAllocation arity grade => value (fun index => (choice.val index).val))
    (s := Finset.univ)
    (fun choice _ => nonnegative (fun index => (choice.val index).val))
    (Finset.mem_univ allocation)

theorem allocatedNormProduct_le_expression {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    {parameters : PhaseParameters} (grade : ℕ) (orders : Fin (arity + 1) → ℕ)
    (total : ∑ index, orders index = grade)
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) :
    allocatedNormProduct orders fields ≤ allocatedGradeExpression grade fields :=
  boundedAllocation_single_le (fun allocated => allocatedNormProduct allocated fields)
    (fun allocated => allocatedNormProduct_nonnegative allocated fields) orders total

end Grad.NonlinearProduct
