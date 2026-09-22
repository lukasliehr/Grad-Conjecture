import ANG24OrdinarySobolevSource
import ANG27SourceDistribution

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.CircularHighWeak
open Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The exact completed AN20 statement on the ordinary single disk. The
constructed derivative is a genuine repeated weak rotation, and its form
equation uses the original source power against the actual H1 test rotation. -/
theorem actualAN20_positive (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) :
    ∃ derivative : highDiskGrade,
      HasH1AngularPower (order + 1) (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩) derivative ∧
      (∀ test : highDiskGrade, robinValue parameter derivative test =
        -inner ℂ (highRotation test) (sourceRotationPower order source.val)) ∧
      ‖derivative‖ ≤ (2 * unitRotationPowerConstant order) * ‖source‖ := by
  have sources : sourceHighBulk order source.val = ⟨unitDiskBulk order source, high⟩ :=
    Subtype.ext (highL2Projection_fixed ⟨unitDiskBulk order source, high⟩)
  refine ⟨angularWeakSolutionPower parameter order source.val, ?_,
    angularWeakSolutionPower_original_functional parameter order source.val high,
    angularWeakSolutionPower_bound parameter order source.val⟩
  have transfer := congrArg (fun value : highDiskL2 => HasH1AngularPower (order + 1)
    (highRobinWeakInverse parameter value) (angularWeakSolutionPower parameter order source.val)) sources
  exact transfer.mp (actualAngularRegularity parameter order source.val).1

/-- AN20's constants precede the real parameter and source. Their dependence
is only on the derivative order, with exactly source grade a−1 for a≥1. -/
theorem actualAN20_uniform (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (parameter : ℝ) (source : unitDiskSobolev order)
      (high : unitDiskBulk order source ∈ highDiskL2),
      ∃ derivative : highDiskGrade,
        HasH1AngularPower (order + 1) (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩) derivative ∧
        (∀ test : highDiskGrade, robinValue parameter derivative test =
          -inner ℂ (highRotation test) (sourceRotationPower order source.val)) ∧
        ‖derivative‖ ≤ constant * ‖source‖ := by
  exact ⟨2 * unitRotationPowerConstant order,
    mul_nonneg (by norm_num) (unitRotationPowerConstant_nonnegative order),
    fun parameter source high => actualAN20_positive parameter order source high⟩

/-- The zero-order companion bound is on every original high L2 source. -/
theorem actualAN20_zero (parameter : ℝ) (source : highDiskL2) :
    ‖highRobinWeakInverse parameter source‖ ≤ 2 * ‖source‖ :=
  weakSolution_bound parameter source

end Grad.CircularHighWeak
