import ANQ7AdditionalAngularValue

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.AnnularSourceGraph

private theorem transfer_collective (energy radial bound size output : ℝ)
    (outputNonnegative : 0 ≤ output) (collective : energy ≤ radial ^ 2 * output ^ 2)
    (estimate : output ≤ bound * size) : energy ≤ (radial * bound) ^ 2 * size ^ 2 :=
  collective.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ outputNonnegative estimate 2)
    (sq_nonneg radial)).trans_eq (by ring))

theorem weakInverse_weighted_value_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * (order + 2)) *
      ‖diskL2Radial lower positive bounded mode
        (highDiskBulk (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩))‖ ^ 2) ≤
      (diskRadialL2Bound * (2 * unitRotationPowerConstant order)) ^ 2 * ‖source‖ ^ 2 := by
  have sources : sourceHighBulk order source.val = ⟨unitDiskBulk order source, high⟩ :=
    Subtype.ext (highL2Projection_fixed ⟨unitDiskBulk order source, high⟩)
  have modeLaw (mode : ℤ) : highDiskMode mode (angularWeakSolutionPower parameter order source.val) =
      (Complex.I * (mode : ℂ)) ^ (order + 1) •
        highDiskMode mode (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩) :=
    (angularWeakSolutionPower_mode parameter order source.val mode).trans
      (congrArg (fun current : highDiskL2 => (Complex.I * (mode : ℂ)) ^ (order + 1) •
        highDiskMode mode (highRobinWeakInverse parameter current)) sources)
  have collective := diskRadial_additional_value_finite lower positive bounded (order + 1)
    (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩)
    (angularWeakSolutionPower parameter order source.val) modeLaw modes
  exact transfer_collective _ diskRadialL2Bound (2 * unitRotationPowerConstant order) ‖source‖
    ‖angularWeakSolutionPower parameter order source.val‖ (norm_nonneg _) collective
    (angularWeakSolutionPower_bound parameter order source.val)

private theorem radialSlope_energy_le (lower : ℝ) (field : WeightedRadialH1 1 lower) :
    ‖weightedRadialCoordinate 1 lower 1 field‖ ^ 2 ≤ ‖field‖ ^ 2 := by
  have norm := weightedRadialH1_norm_sq 1 lower field
  linarith [sq_nonneg ‖weightedRadialCoordinate 1 lower 0 field‖]

/-- Zero and one radial derivative energy at total order s+2, on the
SAME inverse. Both coordinates use the actual r dr storage convention. -/
def inverseZeroOneEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : highDiskL2) (mode : ℤ) : ℝ :=
  |(mode : ℝ)| ^ (2 * (order + 2)) *
    ‖diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2 +
  |(mode : ℝ)| ^ (2 * (order + 1)) *
    ‖weightedRadialCoordinate 1 lower 1
      (diskRadial lower positive bounded mode (highRobinWeakInverse parameter source).val)‖ ^ 2

def zeroOneCollarConstant (order : ℕ) : ℝ :=
  (diskRadialL2Bound * (2 * unitRotationPowerConstant order)) ^ 2 +
    (diskRadialBound * (2 * unitRotationPowerConstant order)) ^ 2

theorem zeroOneCollarConstant_nonnegative (order : ℕ) : 0 ≤ zeroOneCollarConstant order :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weakInverse_zeroOne_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (modes : Finset ℤ) :
    (∑ mode ∈ modes, inverseZeroOneEnergy lower positive bounded parameter order
      ⟨unitDiskBulk order source, high⟩ mode) ≤ zeroOneCollarConstant order * ‖source‖ ^ 2 := by
  have values := weakInverse_weighted_value_finite lower positive bounded parameter order source high modes
  have graph := weakInverse_weighted_radial_finite lower positive bounded parameter order source high modes
  have slopes := Finset.sum_le_sum (s := modes) (fun mode _ =>
    mul_le_mul_of_nonneg_left (radialSlope_energy_le lower
      (diskRadial lower positive bounded mode (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩).val))
      (pow_nonneg (abs_nonneg (mode : ℝ)) (2 * (order + 1))))
  dsimp only [inverseZeroOneEnergy]
  rw [Finset.sum_add_distrib]
  exact (add_le_add values (slopes.trans graph)).trans_eq (add_mul _ _ _).symm

/-- Complete AN20 collar consumer, uniform in k, the collar endpoint and
the angular cutoff: actual |m|^(s+2) values and |m|^(s+1) first slopes are
square summable with only the original source H^s norm. -/
theorem actualCollectiveZeroOneCollar (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) :
    Summable (inverseZeroOneEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩) ∧
      (∑' mode : ℤ, inverseZeroOneEnergy lower positive bounded parameter order
        ⟨unitDiskBulk order source, high⟩ mode) ≤ zeroOneCollarConstant order * ‖source‖ ^ 2 := by
  have nonnegative (mode : ℤ) : 0 ≤ inverseZeroOneEnergy lower positive bounded parameter order
      ⟨unitDiskBulk order source, high⟩ mode :=
    add_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  have finite := weakInverse_zeroOne_finite lower positive bounded parameter order source high
  have summable := summable_of_sum_le nonnegative finite
  exact ⟨summable, summable.tsum_le_of_sum_le finite⟩

end Grad.CircularHighRegularity
