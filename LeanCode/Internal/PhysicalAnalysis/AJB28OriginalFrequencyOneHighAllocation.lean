import AJB21OriginalLowOrderedOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularOrbitGenerators
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation

/-- The complementary frequency power has precisely the opposite
interpolation exponent to the positive coefficient derivative order. -/
theorem frequency_complementary_power (frequency : ℝ) (positive : 0 < frequency)
    (grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade) :
    frequency ^ (grade - order) = (frequency ^ grade) ^ (1 - (order : ℝ) / grade) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul positive.le]
  congr 1
  rw [Nat.cast_sub ordered]
  have nonzero : (grade : ℝ) ≠ 0 := by exact_mod_cast gradePositive.ne'
  field_simp

/-- Original primitive interpolation paired pointwise with the complementary
frequency power. Only one high physical budget occurs. -/
theorem physical_budget_frequency_split (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon frequency : ℝ) (frequencyPositive : 0 < frequency)
    (offset grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade) :
    physicalBudget parameters field rho epsilon (offset + order) * frequency ^ (grade - order) ≤
      physicalInterpolationConstant offset grade *
        (physicalBudget parameters field rho epsilon offset * frequency ^ grade +
          physicalBudget parameters field rho epsilon (offset + grade)) := by
  have thetaNonnegative : 0 ≤ (order : ℝ) / grade := by positivity
  have thetaLeOne : (order : ℝ) / grade ≤ 1 := by
    apply (div_le_one (by exact_mod_cast gradePositive)).2
    exact_mod_cast ordered
  have physical := physical_budget_interpolation offset grade order gradePositive ordered parameters field rho epsilon
  let low := physicalBudget parameters field rho epsilon offset
  let high := physicalBudget parameters field rho epsilon (offset + grade)
  let theta := (order : ℝ) / grade
  have lowNonnegative : 0 ≤ low := physicalBudget_nonnegative _ _ _ _ _
  have highNonnegative : 0 ≤ high := physicalBudget_nonnegative _ _ _ _ _
  have weighted := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr thetaLeOne) thetaNonnegative
    (mul_nonneg lowNonnegative (pow_nonneg frequencyPositive.le grade)) highNonnegative
    (by ring : (1 - theta) + theta = 1)
  have complementary : (low ^ (1 - theta) * high ^ theta) * frequency ^ (grade - order) ≤
      low * frequency ^ grade + high := by
    rw [frequency_complementary_power frequency frequencyPositive grade order gradePositive ordered]
    have identity : (low ^ (1 - theta) * high ^ theta) * (frequency ^ grade) ^ (1 - theta) =
        (low * frequency ^ grade) ^ (1 - theta) * high ^ theta := by
      rw [Real.mul_rpow lowNonnegative (pow_nonneg frequencyPositive.le grade)]
      ring
    rw [identity]
    exact weighted.trans (add_le_add
      (mul_le_of_le_one_left (mul_nonneg lowNonnegative (pow_nonneg frequencyPositive.le grade)) (by linarith : 1 - theta ≤ 1))
      (mul_le_of_le_one_left highNonnegative thetaLeOne))
  have multiplied := mul_le_mul_of_nonneg_right physical (pow_nonneg frequencyPositive.le (grade - order))
  apply multiplied.trans
  have scaled := mul_le_mul_of_nonneg_left complementary
    (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade))
  exact (by simpa only [mul_assoc] using scaled)

end Grad.AnnularOrbitGenerators
