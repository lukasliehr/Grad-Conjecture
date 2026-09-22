import AKBZ2OriginalLowBudgetInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 650000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearProduct Grad.FourierInterpolation

/-- CT4 with the complementary original total derivative order. The two
endpoints are included, and the original phase and analytic width are fixed. -/
theorem originalGrade_complementary_interpolation
    {dimension : ℕ} {parameters : PhaseParameters} (field : ACore parameters dimension)
    (grade order : ℕ) (gradePositive : 0<grade) (orderLe : order≤grade) :
    originalGradeNorm (grade-order) field≤physicalInterpolationConstant 0 grade*
      (originalGradeNorm 0 field^((order:ℝ)/grade)*
        originalGradeNorm grade field^(1-(order:ℝ)/grade)) := by
  have constantOne := physicalInterpolationConstant_one_le 0 grade
  by_cases orderZero : order=0
  · subst order
    simp only [Nat.sub_zero,Nat.cast_zero,zero_div,sub_zero,Real.rpow_zero,Real.rpow_one,one_mul]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative grade field) constantOne
  by_cases orderTop : order=grade
  · subst order
    rw [Nat.sub_self,div_self (by exact_mod_cast gradePositive.ne'),sub_self,Real.rpow_one,Real.rpow_zero,mul_one]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative 0 field) constantOne
  have middlePositive : 0<grade-order := Nat.sub_pos_of_lt (lt_of_le_of_ne orderLe orderTop)
  have middleTop : grade-order<grade := Nat.sub_lt gradePositive (Nat.pos_of_ne_zero orderZero)
  have fraction : interpolationTheta 0 (grade-order) grade=1-(order:ℝ)/grade := by
    unfold interpolationTheta
    simp only [Nat.sub_zero]
    rw [Nat.cast_sub orderLe]
    field_simp
  have bound := original_grade_interpolation middlePositive middleTop field
  rw [fraction,show 1-(1-(order:ℝ)/grade)=(order:ℝ)/grade by ring] at bound
  refine bound.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · simpa only [Nat.zero_add] using originalConstant_le_physical 0 grade (grade-order) (Nat.sub_le _ _)
  · exact mul_nonneg (Real.rpow_nonneg (originalGradeNorm_nonnegative 0 field) _)
      (Real.rpow_nonneg (originalGradeNorm_nonnegative grade field) _)

end Grad.OriginalCartesianTameEstimate
