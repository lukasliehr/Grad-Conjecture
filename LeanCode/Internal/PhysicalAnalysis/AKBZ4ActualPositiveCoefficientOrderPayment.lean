import AKBZ3OriginalComplementaryMixedInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearProduct

/-- Each genuine positive coefficient allocation j pays the complementary
unknown order q-j. The adjustable constant is independent of the original
state, source and unknown; only the fixed low coefficient norm is bounded. -/
theorem originalPositiveOrder_oneHigh
    (offset grade order : ℕ) (gradePositive : 0<grade) (orderPositive : 0<order) (orderLe : order≤grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧
      ∀ (dimension : ℕ) (parameters : PhaseParameters) (coefficient : ACore parameters 3)
        (rho curvature : ℝ) (unknown : ACore parameters dimension),
      physicalBudget parameters coefficient rho curvature offset≤1 →
      (1+physicalBudget parameters coefficient rho curvature (offset+order))*originalGradeNorm (grade-order) unknown≤
        epsilon*originalGradeNorm grade unknown+
          remainder*((1+physicalBudget parameters coefficient rho curvature (offset+grade))*originalGradeNorm 0 unknown) := by
  let theta := (order:ℝ)/grade
  have thetaPositive : 0<theta := div_pos (by exact_mod_cast orderPositive) (by exact_mod_cast gradePositive)
  have thetaOne : theta≤1 := (div_le_one (by exact_mod_cast gradePositive : 0<(grade:ℝ))).mpr (by exact_mod_cast orderLe)
  let constant := (1+physicalInterpolationConstant offset grade)*physicalInterpolationConstant 0 grade
  have constantNonnegative : 0≤constant := mul_nonneg
    (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)))
    (zero_le_one.trans (physicalInterpolationConstant_one_le 0 grade))
  obtain ⟨remainder,nonnegative,adjust⟩ := positiveOrder_adjustable_constant theta constant epsilon
    thetaPositive thetaOne constantNonnegative epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro dimension parameters coefficient rho curvature unknown lowBound
  let high := 1+physicalBudget parameters coefficient rho curvature (offset+grade)
  have highNonnegative : 0≤high := add_nonneg zero_le_one (physicalBudget_nonnegative parameters coefficient rho curvature (offset+grade))
  have coefficientBound := originalLowBudget_interpolation parameters coefficient rho curvature offset grade order gradePositive orderLe lowBound
  have unknownBound := originalGrade_complementary_interpolation unknown grade order gradePositive orderLe
  have product := mul_le_mul coefficientBound unknownBound
    (originalGradeNorm_nonnegative (grade-order) unknown)
    (mul_nonneg (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)))
      (Real.rpow_nonneg highNonnegative theta))
  have rearrange :
      ((1+physicalInterpolationConstant offset grade)*high^theta)*
        (physicalInterpolationConstant 0 grade*(originalGradeNorm 0 unknown^theta*originalGradeNorm grade unknown^(1-theta)))=
      constant*(originalGradeNorm grade unknown^(1-theta)*(high*originalGradeNorm 0 unknown)^theta) := by
    rw [Real.mul_rpow highNonnegative (originalGradeNorm_nonnegative 0 unknown)]
    dsimp only [constant]
    ring
  exact product.trans (rearrange.le.trans
    (adjust (originalGradeNorm grade unknown) (high*originalGradeNorm 0 unknown)
      (originalGradeNorm_nonnegative grade unknown) (mul_nonneg highNonnegative (originalGradeNorm_nonnegative 0 unknown))))

end Grad.OriginalCartesianTameEstimate
