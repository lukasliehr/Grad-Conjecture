import AKDK8JointPrimitiveTerminalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.OriginalCartesianTameEstimate Grad.GaugeCoefficients.Physical.Allocation

/-- Pure tangential terminal allocation is scalar Fourier algebra and does
not require extending the native solution in the radial variable. -/
theorem pureFrequency_jointAllocation (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (offset grade order power : ℕ) (gradePositive : 0<grade) (paid : order+power≤grade)
    (low : physicalBudget parameters field rho epsilon offset≤1)
    (frequency : ℝ) (frequencyOne : 1≤frequency) :
    (1+physicalBudget parameters field rho epsilon (offset+order))*frequency^power ≤
      (1+physicalInterpolationConstant offset grade)*(frequency^grade+
        (1+physicalBudget parameters field rho epsilon (offset+grade))) := by
  have frequencyPositive : 0<frequency := zero_lt_one.trans_le frequencyOne
  have gradeReal : 0<(grade:ℝ) := by exact_mod_cast gradePositive
  have orderLe : order≤grade := by omega
  have theta0 : 0≤(order:ℝ)/grade := div_nonneg (Nat.cast_nonneg _) gradeReal.le
  have theta1 : (order:ℝ)/grade≤1 := (div_le_one gradeReal).mpr (by exact_mod_cast orderLe)
  let high := 1+physicalBudget parameters field rho epsilon (offset+grade)
  have high0 : 0≤high := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have exponent : (grade:ℝ)*(1-(order:ℝ)/grade)=(grade-order:ℕ) := by
    rw [Nat.cast_sub orderLe]
    field_simp
  have complement : frequency^(grade-order)=(frequency^grade)^(1-(order:ℝ)/grade) := by
    rw [← Real.rpow_natCast frequency grade,← Real.rpow_mul frequencyPositive.le,exponent,Real.rpow_natCast]
  have coefficient := originalLowBudget_interpolation parameters field rho epsilon offset grade order gradePositive orderLe low
  have powerBound : frequency^power≤frequency^(grade-order) := pow_le_pow_right₀ frequencyOne (by omega)
  have multiplied := mul_le_mul coefficient powerBound (pow_nonneg frequencyPositive.le _)
    (mul_nonneg (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le _ _)))
      (Real.rpow_nonneg high0 _))
  rw [complement] at multiplied
  have geometric := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr theta1) theta0
    (pow_nonneg frequencyPositive.le grade) high0 (by ring : (1-(order:ℝ)/grade)+(order:ℝ)/grade=1)
  have endpoints : (frequency^grade)^(1-(order:ℝ)/grade)*high^((order:ℝ)/grade) ≤ frequency^grade+high := by
    exact geometric.trans (add_le_add
      (mul_le_of_le_one_left (pow_nonneg frequencyPositive.le _) (by linarith : 1-(order:ℝ)/grade≤1))
      (mul_le_of_le_one_left high0 theta1))
  have result := mul_le_mul_of_nonneg_left endpoints
    (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)))
  dsimp only [high] at result ⊢
  nlinarith only [multiplied,result]

end Grad.OriginalTerminalAllocation
