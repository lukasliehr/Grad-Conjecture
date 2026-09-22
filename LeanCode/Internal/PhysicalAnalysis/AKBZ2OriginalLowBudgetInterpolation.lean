import AKBZ1AdjustablePositiveOrderInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearProduct

/-- CT5 at the exact original coefficient budget. Only the fixed low
coefficient norm is bounded; the high norm remains unrestricted. -/
theorem originalLowBudget_interpolation
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (offset grade order : ℕ) (gradePositive : 0<grade) (orderLe : order≤grade)
    (lowBound : physicalBudget parameters field rho epsilon offset≤1) :
    1+physicalBudget parameters field rho epsilon (offset+order)≤
      (1+physicalInterpolationConstant offset grade)*
        (1+physicalBudget parameters field rho epsilon (offset+grade))^((order:ℝ)/grade) := by
  have gradeReal : 0<(grade:ℝ) := by exact_mod_cast gradePositive
  have thetaNonnegative : 0≤(order:ℝ)/grade := div_nonneg (Nat.cast_nonneg _) gradeReal.le
  have thetaOne : (order:ℝ)/grade≤1 := (div_le_one gradeReal).mpr (by exact_mod_cast orderLe)
  have constantNonnegative : 0≤physicalInterpolationConstant offset grade :=
    zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)
  have lowPower : physicalBudget parameters field rho epsilon offset^(1-(order:ℝ)/grade)≤1 := by
    have bound := Real.rpow_le_rpow (physicalBudget_nonnegative parameters field rho epsilon offset)
      lowBound (sub_nonneg.mpr thetaOne)
    simpa only [Real.one_rpow] using bound
  have highPower := Real.rpow_le_rpow
    (physicalBudget_nonnegative parameters field rho epsilon (offset+grade))
    (le_add_of_nonneg_left zero_le_one : physicalBudget parameters field rho epsilon (offset+grade)≤
      1+physicalBudget parameters field rho epsilon (offset+grade)) thetaNonnegative
  have middleBound := physical_budget_interpolation offset grade order gradePositive orderLe parameters field rho epsilon
  have paid : physicalBudget parameters field rho epsilon (offset+order)≤
      physicalInterpolationConstant offset grade*
        (1+physicalBudget parameters field rho epsilon (offset+grade))^((order:ℝ)/grade) := by
    refine middleBound.trans (mul_le_mul_of_nonneg_left ?_ constantNonnegative)
    exact (mul_le_mul lowPower highPower
      (Real.rpow_nonneg (physicalBudget_nonnegative parameters field rho epsilon (offset+grade)) _) zero_le_one).trans_eq
      (one_mul _)
  have onePower : 1≤(1+physicalBudget parameters field rho epsilon (offset+grade))^((order:ℝ)/grade) :=
    Real.one_le_rpow (le_add_of_nonneg_right (physicalBudget_nonnegative parameters field rho epsilon (offset+grade))) thetaNonnegative
  calc
    _≤(1+physicalBudget parameters field rho epsilon (offset+grade))^((order:ℝ)/grade)+
        physicalInterpolationConstant offset grade*(1+physicalBudget parameters field rho epsilon (offset+grade))^((order:ℝ)/grade) :=
      add_le_add onePower paid
    _=_ := by ring

end Grad.OriginalCartesianTameEstimate
