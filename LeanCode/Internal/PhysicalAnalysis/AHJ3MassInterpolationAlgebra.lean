import AHJ2MassGradeComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.FourierInterpolation Grad.GaugeCoefficients.Physical.Allocation

theorem apMassPower_interpolation {low middle high : ℕ} (mass : ℝ) (positive : 0 < mass)
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    mass ^ (middle - low) = (mass ^ (high - low)) ^ interpolationTheta low middle high := by
  rw [← Real.rpow_natCast mass (middle - low), ← Real.rpow_natCast mass (high - low),
    ← Real.rpow_mul positive.le]
  congr 1
  unfold interpolationTheta
  have denominator : ((high - low : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt (lowMiddle.trans middleHigh)).ne'
  field_simp

theorem apMassPower_complement {low middle high : ℕ} (mass : ℝ) (positive : 0 < mass)
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    mass ^ (high - middle) = (mass ^ (high - low)) ^ (1 - interpolationTheta low middle high) := by
  rw [← Real.rpow_natCast mass (high - middle), ← Real.rpow_natCast mass (high - low),
    ← Real.rpow_mul positive.le]
  congr 1
  have differences : (high - low : ℕ) = (middle - low) + (high - middle) := by omega
  have realDifferences := congrArg (fun n : ℕ => (n : ℝ)) differences
  push_cast at realDifferences
  unfold interpolationTheta
  have denominator : ((high - low : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt (lowMiddle.trans middleHigh)).ne'
  field_simp
  nlinarith

/-- The missing mass power has exactly the same interpolation exponent as
the derivative grade; zero low norms are included. -/
theorem apMassPower_product_interpolation {low middle high : ℕ}
    (mass value : ℝ) (positive : 0 < mass) (nonnegative : 0 ≤ value)
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    mass ^ (middle - low) * value =
      value ^ (1 - interpolationTheta low middle high) *
        (mass ^ (high - low) * value) ^ interpolationTheta low middle high := by
  rw [Real.mul_rpow (pow_nonneg positive.le _) nonnegative,
    ← apMassPower_interpolation mass positive lowMiddle middleHigh]
  calc
    _ = mass ^ (middle - low) *
        (value ^ (1 - interpolationTheta low middle high) * value ^ interpolationTheta low middle high) := by
      rw [nonnegative_interpolation_self nonnegative
        (interpolationTheta_pos lowMiddle middleHigh) (interpolationTheta_lt_one lowMiddle middleHigh)]
    _ = _ := by ring

/-- Weighted arithmetic-geometric mean absorbs each intermediate ordinary
disk derivative into the two endpoint terms, uniformly in the mass. -/
theorem apMassPower_mixed_le_endpoints {low middle high : ℕ}
    (mass first second : ℝ) (positive : 0 < mass) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (lowMiddle : low < middle) (middleHigh : middle < high) :
    mass ^ (high - middle) *
      (first ^ (1 - interpolationTheta low middle high) * second ^ interpolationTheta low middle high) ≤
      mass ^ (high - low) * first + second := by
  let theta := interpolationTheta low middle high
  have thetaPositive : 0 < theta := interpolationTheta_pos lowMiddle middleHigh
  have thetaLess : theta < 1 := interpolationTheta_lt_one lowMiddle middleHigh
  have identity : mass ^ (high - middle) * (first ^ (1 - theta) * second ^ theta) =
      (mass ^ (high - low) * first) ^ (1 - theta) * second ^ theta := by
    rw [Real.mul_rpow (pow_nonneg positive.le _) firstNonnegative,
      ← apMassPower_complement mass positive lowMiddle middleHigh]
    ring
  rw [identity]
  have firstTermNonnegative : 0 ≤ mass ^ (high - low) * first := mul_nonneg (pow_nonneg positive.le _) firstNonnegative
  have weighted := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr thetaLess.le)
    thetaPositive.le firstTermNonnegative secondNonnegative (by ring : (1 - theta) + theta = 1)
  apply weighted.trans
  exact add_le_add
    (mul_le_of_le_one_left firstTermNonnegative (by linarith : 1 - theta ≤ 1))
    (mul_le_of_le_one_left secondNonnegative thetaLess.le)

end Grad.GaugeCoefficients.Physical.RadialLedger
