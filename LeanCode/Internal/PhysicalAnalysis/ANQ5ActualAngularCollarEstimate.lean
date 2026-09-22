import ANQ4WeightedRadialEnergy

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.AnnularSourceGraph

private theorem collective_bound_transfer (energy radial bound size output : ℝ)
    (outputNonnegative : 0 ≤ output) (collective : energy ≤ radial ^ 2 * output ^ 2)
    (estimate : output ≤ bound * size) : energy ≤ (radial * bound) ^ 2 * size ^ 2 := by
  have square := pow_le_pow_left₀ outputNonnegative estimate 2
  exact collective.trans ((mul_le_mul_of_nonneg_left square (sq_nonneg radial)).trans_eq (by ring))

/-- AN20 gives actual collective angular-weighted radial value and slope
estimates on the original ordinary source grade a−1. The coefficient set
and its largest frequency never enter the constant. -/
theorem weakInverse_weighted_radial_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * (order + 1)) *
      ‖diskRadial lower positive bounded mode
        (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩).val‖ ^ 2) ≤
      (diskRadialBound * (2 * unitRotationPowerConstant order)) ^ 2 * ‖source‖ ^ 2 := by
  have sources : sourceHighBulk order source.val = ⟨unitDiskBulk order source, high⟩ :=
    Subtype.ext (highL2Projection_fixed ⟨unitDiskBulk order source, high⟩)
  have modeLaw (mode : ℤ) : highDiskMode mode (angularWeakSolutionPower parameter order source.val) =
      (Complex.I * (mode : ℂ)) ^ (order + 1) •
        highDiskMode mode (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩) :=
    (angularWeakSolutionPower_mode parameter order source.val mode).trans
      (congrArg (fun current : highDiskL2 => (Complex.I * (mode : ℂ)) ^ (order + 1) •
        highDiskMode mode (highRobinWeakInverse parameter current)) sources)
  have collective := diskRadial_weighted_finite_energy lower positive bounded (order + 1)
    (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩)
    (angularWeakSolutionPower parameter order source.val) modeLaw modes
  exact collective_bound_transfer _ diskRadialBound (2 * unitRotationPowerConstant order) ‖source‖
    ‖angularWeakSolutionPower parameter order source.val‖ (norm_nonneg _) collective
    (angularWeakSolutionPower_bound parameter order source.val)

theorem weakInverse_weighted_radial_summable (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) :
    Summable (fun mode : ℤ => |(mode : ℝ)| ^ (2 * (order + 1)) *
      ‖diskRadial lower positive bounded mode
        (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩).val‖ ^ 2) :=
  summable_of_sum_le (fun _ => mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
    (weakInverse_weighted_radial_finite lower positive bounded parameter order source high)

theorem weakInverse_weighted_radial_total (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) :
    (∑' mode : ℤ, |(mode : ℝ)| ^ (2 * (order + 1)) *
      ‖diskRadial lower positive bounded mode
        (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩).val‖ ^ 2) ≤
      (diskRadialBound * (2 * unitRotationPowerConstant order)) ^ 2 * ‖source‖ ^ 2 :=
  (weakInverse_weighted_radial_summable lower positive bounded parameter order source high).tsum_le_of_sum_le
    (weakInverse_weighted_radial_finite lower positive bounded parameter order source high)

end Grad.CircularHighRegularity
