import AKDK1OriginalSourceInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearProduct
open Grad.QuotientProjection Grad.OriginalCartesianTameEstimate

/-- Positive coefficient orders are jointly allocated against the SAME
original four-row source, retaining the independent F4 endpoint. -/
theorem originalSource_positiveOrder_oneHigh
    (offset grade order : ℕ) (gradePositive : 0<grade) (orderPositive : 0<order) (orderLe : order≤grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧
      ∀ (parameters : PhaseParameters) (coefficient : ACore parameters 3)
        (rho curvature : ℝ) (source : SmoothQuotient parameters),
      physicalBudget parameters coefficient rho curvature offset≤1 →
      (1+physicalBudget parameters coefficient rho curvature (offset+order))*‖quotientEta parameters (4+(grade-order)) source‖≤
        epsilon*‖quotientEta parameters (4+grade) source‖+
          remainder*((1+physicalBudget parameters coefficient rho curvature (offset+grade))*‖quotientEta parameters 4 source‖) := by
  let theta := (order:ℝ)/grade
  have thetaPositive : 0<theta := div_pos (by exact_mod_cast orderPositive) (by exact_mod_cast gradePositive)
  have thetaOne : theta≤1 := (div_le_one (by exact_mod_cast gradePositive : 0<(grade:ℝ))).mpr (by exact_mod_cast orderLe)
  let constant := (1+physicalInterpolationConstant offset grade)*(2*physicalInterpolationConstant 4 grade)
  have constantNonnegative : 0≤constant := mul_nonneg
    (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)))
    (mul_nonneg (by norm_num) (zero_le_one.trans (physicalInterpolationConstant_one_le 4 grade)))
  obtain ⟨remainder,nonnegative,adjust⟩ := positiveOrder_adjustable_constant theta constant epsilon
    thetaPositive thetaOne constantNonnegative epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro parameters coefficient rho curvature source lowBound
  let high := 1+physicalBudget parameters coefficient rho curvature (offset+grade)
  have highNonnegative : 0≤high := add_nonneg zero_le_one (physicalBudget_nonnegative parameters coefficient rho curvature (offset+grade))
  have coefficientBound := originalLowBudget_interpolation parameters coefficient rho curvature offset grade order gradePositive orderLe lowBound
  have unknownBound := originalSource_complementary parameters source grade order gradePositive orderLe
  have product := mul_le_mul coefficientBound unknownBound
    (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)))
      (Real.rpow_nonneg highNonnegative theta))
  have rearrange :
      ((1+physicalInterpolationConstant offset grade)*high^theta)*
        ((2*physicalInterpolationConstant 4 grade)*(‖quotientEta parameters 4 source‖^theta*‖quotientEta parameters (4+grade) source‖^(1-theta)))=
      constant*(‖quotientEta parameters (4+grade) source‖^(1-theta)*(high*‖quotientEta parameters 4 source‖)^theta) := by
    rw [Real.mul_rpow highNonnegative (norm_nonneg _)]
    dsimp only [constant]
    ring
  exact product.trans (rearrange.le.trans
    (adjust (‖quotientEta parameters (4+grade) source‖) (high*‖quotientEta parameters 4 source‖)
      (norm_nonneg _) (mul_nonneg highNonnegative (norm_nonneg _))))

end Grad.OriginalTerminalAllocation
