import AKCK11LiteralKnownRowConsumer
import AKBZ4ActualPositiveCoefficientOrderPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.NonlinearProduct Grad.FourierInterpolation Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation
open Grad.OriginalCartesianTameEstimate

/-- Complementary interpolation retains any original base grade. -/
theorem originalGrade_shifted_complementary
    {dimension : ℕ} {parameters : PhaseParameters} (field : ACore parameters dimension)
    (offset grade order : ℕ) (gradePositive : 0<grade) (orderLe : order≤grade) :
    originalGradeNorm (offset+(grade-order)) field≤physicalInterpolationConstant offset grade*
      (originalGradeNorm offset field^((order:ℝ)/grade)*
        originalGradeNorm (offset+grade) field^(1-(order:ℝ)/grade)) := by
  have constantOne := physicalInterpolationConstant_one_le offset grade
  by_cases orderZero : order=0
  · subst order
    simp only [Nat.sub_zero,Nat.cast_zero,zero_div,sub_zero,Real.rpow_zero,Real.rpow_one,one_mul]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative _ field) constantOne
  by_cases orderTop : order=grade
  · subst order
    rw [Nat.sub_self,Nat.add_zero,div_self (by exact_mod_cast gradePositive.ne'),sub_self,Real.rpow_one,Real.rpow_zero,mul_one]
    exact le_mul_of_one_le_left (originalGradeNorm_nonnegative _ field) constantOne
  have strictLow : offset<offset+(grade-order) := by omega
  have strictHigh : offset+(grade-order)<offset+grade := by omega
  have fraction : interpolationTheta offset (offset+(grade-order)) (offset+grade)=1-(order:ℝ)/grade := by
    unfold interpolationTheta
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.cast_sub orderLe]
    field_simp
  have bound := original_grade_interpolation strictLow strictHigh field
  rw [fraction,show 1-(1-(order:ℝ)/grade)=(order:ℝ)/grade by ring] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right
    (originalConstant_le_physical offset grade (grade-order) (Nat.sub_le _ _))
    (mul_nonneg (Real.rpow_nonneg (originalGradeNorm_nonnegative _ field) _)
      (Real.rpow_nonneg (originalGradeNorm_nonnegative _ field) _)))

/-- Actual four-row Hilbert source interpolation, at the original width and
with the independent F4 base used by the fixed-collar terminal estimates. -/
theorem originalSource_complementary (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (grade order : ℕ) (gradePositive : 0<grade) (orderLe : order≤grade) :
    ‖quotientEta parameters (4+(grade-order)) source‖ ≤
      (2*physicalInterpolationConstant 4 grade)*
        (‖quotientEta parameters 4 source‖^((order:ℝ)/grade)*
          ‖quotientEta parameters (4+grade) source‖^(1-(order:ℝ)/grade)) := by
  have theta0 : 0≤(order:ℝ)/grade := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have theta1 : (order:ℝ)/grade≤1 := (div_le_one (by exact_mod_cast gradePositive : 0<(grade:ℝ))).mpr (by exact_mod_cast orderLe)
  have constant0 : 0≤physicalInterpolationConstant 4 grade := zero_le_one.trans (physicalInterpolationConstant_one_le _ _)
  have bound (row : Fin 4) : originalGradeNorm (4+(grade-order)) (source row) ≤
      physicalInterpolationConstant 4 grade *
        (‖quotientEta parameters 4 source‖^((order:ℝ)/grade)*
          ‖quotientEta parameters (4+grade) source‖^(1-(order:ℝ)/grade)) := by
    refine (originalGrade_shifted_complementary (source row) 4 grade order gradePositive orderLe).trans ?_
    apply mul_le_mul_of_nonneg_left _ constant0
    exact mul_le_mul
      (Real.rpow_le_rpow (originalGradeNorm_nonnegative _ _) (originalScalarCore_norm_le parameters 4 source row) theta0)
      (Real.rpow_le_rpow (originalGradeNorm_nonnegative _ _) (originalScalarCore_norm_le parameters (4+grade) source row) (sub_nonneg.mpr theta1))
      (Real.rpow_nonneg (originalGradeNorm_nonnegative _ _) _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have total := quotientNorm_le_two_mul parameters (4+(grade-order)) source _
    (mul_nonneg constant0 (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))) bound
  exact total.trans_eq (by ring)

end Grad.OriginalTerminalAllocation
