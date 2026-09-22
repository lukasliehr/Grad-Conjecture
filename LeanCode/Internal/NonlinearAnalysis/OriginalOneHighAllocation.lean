import OriginalInterpolation

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.CartesianState Grad.FourierInterpolation

def allocationInterpolationConstant (grade : ℕ) : ℝ :=
  1 + ∑ order : Fin (grade + 1), originalInterpolationConstant 3 (order.val + 3) (grade + 3)

theorem allocationInterpolationConstant_one_le (grade : ℕ) :
    1 ≤ allocationInterpolationConstant grade := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg
    (fun order _ => originalInterpolationConstant_nonnegative _ _ _))

theorem originalInterpolationConstant_le_allocation (grade order : ℕ) (orderLe : order ≤ grade) :
    originalInterpolationConstant 3 (order + 3) (grade + 3) ≤ allocationInterpolationConstant grade := by
  have single := Finset.single_le_sum
    (f := fun index : Fin (grade + 1) => originalInterpolationConstant 3 (index.val + 3) (grade + 3))
    (s := Finset.univ) (fun index _ => originalInterpolationConstant_nonnegative _ _ _)
    (Finset.mem_univ (⟨order, by omega⟩ : Fin (grade + 1)))
  exact single.trans (le_add_of_nonneg_left zero_le_one)

theorem original_allocated_interpolation {dimension : ℕ} {parameters : PhaseParameters}
    (grade order : ℕ) (gradePositive : 0 < grade) (orderLe : order ≤ grade)
    (field : ACore parameters dimension) :
    originalGradeNorm (order + 3) field ≤ allocationInterpolationConstant grade *
      (originalGradeNorm 3 field ^ (1 - (order : ℝ) / grade) *
        originalGradeNorm (grade + 3) field ^ ((order : ℝ) / grade)) := by
  by_cases orderZero : order = 0
  · subst order
    simp only [zero_add, Nat.cast_zero, zero_div, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative _ _)
      (allocationInterpolationConstant_one_le _)
  by_cases orderTop : order = grade
  · subst order
    rw [div_self (by exact_mod_cast gradePositive.ne'), sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative _ _)
      (allocationInterpolationConstant_one_le _)
  have strictLow : 3 < order + 3 := by omega
  have strictHigh : order + 3 < grade + 3 := by omega
  have thetaEquality : interpolationTheta 3 (order + 3) (grade + 3) = (order : ℝ) / grade := by
    simp [interpolationTheta]
  have interpolation := original_grade_interpolation strictLow strictHigh field
  rw [thetaEquality] at interpolation
  exact interpolation.trans (mul_le_mul_of_nonneg_right
    (originalInterpolationConstant_le_allocation grade order orderLe)
    (mul_nonneg (Real.rpow_nonneg (originalGradeNorm_nonnegative _ _) _)
      (Real.rpow_nonneg (originalGradeNorm_nonnegative _ _) _)))

/-- Actual original-ACore interpolation closes the finite allocation step.
This is internal to Q1–Q2: it does not assume or assert the missing product
convolution estimate. Zero low norms are included by the accepted AQ3 lemma. -/
theorem original_allocated_product_one_high {arity : ℕ} {dimensions : Fin arity → ℕ}
    {parameters : PhaseParameters} (grade : ℕ) (gradePositive : 0 < grade)
    (orders : Fin arity → ℕ) (allocated : ∑ index, orders index = grade)
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) :
    (∏ index, originalGradeNorm (orders index + 3) (fields index)) ≤
      allocationInterpolationConstant grade ^ arity *
        ∑ index, originalGradeNorm (grade + 3) (fields index) *
          ∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other) := by
  have orderLe (index : Fin arity) : orders index ≤ grade := by
    rw [← allocated]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have constantNonnegative : 0 ≤ allocationInterpolationConstant grade :=
    zero_le_one.trans (allocationInterpolationConstant_one_le grade)
  calc
    _ ≤ ∏ index, allocationInterpolationConstant grade *
        (originalGradeNorm 3 (fields index) ^ (1 - (orders index : ℝ) / grade) *
          originalGradeNorm (grade + 3) (fields index) ^ ((orders index : ℝ) / grade)) :=
      Finset.prod_le_prod (fun _ _ => originalGradeNorm_nonnegative _ _)
        (fun index _ => original_allocated_interpolation grade (orders index) gradePositive (orderLe index) (fields index))
    _ = allocationInterpolationConstant grade ^ arity *
        ∏ index, originalGradeNorm 3 (fields index) ^ (1 - (orders index : ℝ) / grade) *
          originalGradeNorm (grade + 3) (fields index) ^ ((orders index : ℝ) / grade) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Grad.TameAllocation.exact_natural_allocation
        (fun index => originalGradeNorm 3 (fields index))
        (fun index => originalGradeNorm (grade + 3) (fields index)) orders grade gradePositive allocated
        (fun _ => originalGradeNorm_nonnegative _ _) (fun _ => originalGradeNorm_nonnegative _ _))
      (pow_nonneg constantNonnegative _)

end Grad.NonlinearProduct
