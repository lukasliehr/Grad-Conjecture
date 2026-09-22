import ProductFiniteAllocations

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.CartesianState

def oneHighExpression {arity : ℕ} {dimensions : Fin arity → ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (fields : (index : Fin arity) → ACore parameters (dimensions index)) : ℝ :=
  ∑ index, originalGradeNorm (grade + 3) (fields index) *
    ∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other)

theorem oneHighExpression_nonnegative {arity : ℕ} {dimensions : Fin arity → ℕ}
    {parameters : PhaseParameters} (grade : ℕ)
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) :
    0 ≤ oneHighExpression grade fields := Finset.sum_nonneg (fun _ _ =>
  mul_nonneg (originalGradeNorm_nonnegative _ _)
    (Finset.prod_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _)))

theorem original_allocated_product_all_grades {arity : ℕ} {dimensions : Fin arity → ℕ}
    {parameters : PhaseParameters} (positiveArity : 0 < arity) (grade : ℕ)
    (orders : Fin arity → ℕ) (allocated : ∑ index, orders index = grade)
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) :
    (∏ index, originalGradeNorm (orders index + 3) (fields index)) ≤
      allocationInterpolationConstant grade ^ arity * oneHighExpression grade fields := by
  classical
  by_cases positiveGrade : 0 < grade
  · exact original_allocated_product_one_high grade positiveGrade orders allocated fields
  have gradeZero : grade = 0 := by omega
  rw [gradeZero] at allocated ⊢
  have eachZero (index : Fin arity) : orders index = 0 := by
    have bounded := Finset.single_le_sum (f := orders) (s := Finset.univ)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
    rw [allocated] at bounded
    omega
  simp only [eachZero, zero_add]
  have oneTerm : (∏ index, originalGradeNorm 3 (fields index)) ≤ oneHighExpression 0 fields := by
    let chosen : Fin arity := ⟨0, positiveArity⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun index => originalGradeNorm 3 (fields index))
      (Finset.mem_univ chosen)]
    exact Finset.single_le_sum (f := fun index : Fin arity => originalGradeNorm 3 (fields index) *
      ∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other)) (s := Finset.univ)
      (fun index _ => mul_nonneg (originalGradeNorm_nonnegative _ _)
      (Finset.prod_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _))) (Finset.mem_univ chosen)
  exact oneTerm.trans (le_mul_of_one_le_left (oneHighExpression_nonnegative _ _)
    (one_le_pow₀ (allocationInterpolationConstant_one_le _)))

end Grad.NonlinearProduct
