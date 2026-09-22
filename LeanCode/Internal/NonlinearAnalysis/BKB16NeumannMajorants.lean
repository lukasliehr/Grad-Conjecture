import BKB15KernelPowerBounds

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The literal AE7 inverse-series constant. -/
def fullKernelNeumannConstant (moment : ℕ) (low : ℝ) : ℝ :=
  ∑' exponent : ℕ,
    ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent

theorem fullKernelNeumannMajorant_summable (moment : ℕ) (low : ℝ)
    (lowNonnegative : 0 ≤ low) (lowSmall : low < 1) :
    Summable (fun exponent : ℕ =>
      ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent) := by
  by_cases lowZero : low = 0
  · refine (hasSum_sum_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_).summable
    intro exponent outside
    have nonzero : exponent ≠ 0 := by
      intro zero
      exact outside (Finset.mem_singleton.mpr zero)
    rw [lowZero, zero_pow nonzero, mul_zero]
  · have lowPositive : 0 < low := lt_of_le_of_ne lowNonnegative (Ne.symm lowZero)
    have shifted : Summable (fun exponent : ℕ =>
        ((exponent + 1 : ℕ) : ℝ) ^ (moment + 1) * low ^ (exponent + 1)) := by
      have base : Summable (fun total : ℕ =>
          (total : ℝ) ^ (moment + 1) * low ^ total) :=
        summable_pow_mul_geometric_of_norm_lt_one (moment + 1)
          (by rwa [Real.norm_eq_abs, abs_of_nonneg lowNonnegative])
      exact base.comp_injective Nat.succ_injective
    have divided : Summable (fun exponent : ℕ =>
        (((exponent + 1 : ℕ) : ℝ) ^ (moment + 1) * low ^ (exponent + 1)) *
          low⁻¹) := shifted.mul_right low⁻¹
    apply divided.congr
    intro exponent
    have cast : ((exponent + 1 : ℕ) : ℝ) = (exponent : ℝ) + 1 := by
      push_cast
      ring
    rw [cast, pow_succ]
    field_simp
    rw [pow_succ']

theorem fullKernelMoment_entryNorm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    kernel.entryNorm shift ≤ fullKernelMoment parameters 0 kernel := by
  have weighted : kernel.entryNorm shift ≤
      boundaryCoefficientPhaseCost parameters shift * kernel.entryNorm shift := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (boundaryCoefficientPhaseCost_one_le parameters shift)
      (fullKernelEntryNorm_nonnegative kernel shift)
  apply weighted.trans
  unfold fullKernelMoment
  simpa only [pow_zero, mul_one] using
    (kernel.moments 0).le_tsum shift (fun other _ =>
      mul_nonneg
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters other)
          (pow_nonneg (annularFrequency_pos other).le 0))
        (fullKernelEntryNorm_nonnegative kernel other))

theorem fullKernelPower_theta_moment_le {dimension : ℕ}
    (parameters : PhaseParameters) (moment exponent : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low) :
    fullKernelMoment parameters moment (fullKernelPower kernel exponent) ≤
      ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent *
        fullKernelMoment parameters moment kernel := by
  have lowNonnegative :=
    (fullKernelMoment_nonnegative parameters 0 kernel).trans lowBound
  have powerBound := pow_le_pow_left₀
    (fullKernelMoment_nonnegative parameters 0 kernel) lowBound exponent
  apply (fullKernelPower_moment_le parameters moment exponent kernel).trans
  calc
    ((exponent : ℝ) + 1) ^ (moment + 1) *
          (fullKernelMoment parameters 0 kernel ^ exponent *
            fullKernelMoment parameters moment kernel) ≤
        ((exponent : ℝ) + 1) ^ (moment + 1) *
          (low ^ exponent * fullKernelMoment parameters moment kernel) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right powerBound
          (fullKernelMoment_nonnegative parameters moment kernel)
      · positivity
    _ = _ := by ring

theorem fullKernelPower_entryNorm_summable {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (shift : ℤ × ℤ) :
    Summable (fun exponent : ℕ =>
      (fullKernelPower kernel exponent).entryNorm shift) := by
  have lowNonnegative :=
    (fullKernelMoment_nonnegative parameters 0 kernel).trans lowBound
  have scalarSummable :=
    (fullKernelNeumannMajorant_summable 0 low lowNonnegative lowSmall).mul_right
      (fullKernelMoment parameters 0 kernel)
  apply Summable.of_nonneg_of_le
    (fun exponent => fullKernelEntryNorm_nonnegative
      (fullKernelPower kernel exponent) shift)
    (fun exponent => ?_) scalarSummable
  exact (fullKernelMoment_entryNorm_le parameters
    (fullKernelPower kernel exponent) shift).trans
      (fullKernelPower_theta_moment_le parameters 0 exponent kernel low lowBound)

theorem fullKernelPower_entry_summable {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (shift input : ℤ × ℤ) :
    Summable (fun exponent : ℕ =>
      (fullKernelPower kernel exponent).entry shift input) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun exponent => norm_nonneg _)
    (fun exponent => (fullKernelPower kernel exponent).entry_le shift input)
    (fullKernelPower_entryNorm_summable parameters kernel low lowBound lowSmall shift)

end Grad.BoundaryKernelAction
