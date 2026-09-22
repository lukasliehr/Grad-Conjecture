import ANG17FirstCompletedDerivative
import ANG21HighSourcePowers

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.CircularHighWeak
open Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated

theorem highRobinWeakInverse_mode_transfer (parameter : ℝ) (mode : ℤ) (scalar : ℂ)
    (first second : highDiskL2)
    (coefficient : diskMode mode second.val = scalar • diskMode mode first.val) :
    highDiskMode mode (highRobinWeakInverse parameter second) =
      scalar • highDiskMode mode (highRobinWeakInverse parameter first) := by
  have sources : highL2Mode mode second = scalar • highL2Mode mode first := Subtype.ext coefficient
  exact (highRobinWeakInverse_angular parameter mode second).trans
    ((congrArg (highRobinWeakInverse parameter) sources).trans
      (((highRobinWeakInverse parameter).map_smul scalar (highL2Mode mode first)).trans
        (congrArg (fun value : highDiskGrade => scalar • value) (highRobinWeakInverse_angular parameter mode first).symm)))

/-- Candidate R^(s+1)z constructed from genuine completed R^sF, with no
extra source derivative and no auxiliary high Sobolev norm. -/
def angularWeakSolutionPower (parameter : ℝ) (order : ℕ) (source : apGrade 1 0 0 1 1 order) : highDiskGrade :=
  firstAngularWeakSolution parameter (sourceHighPower order source)

theorem angularWeakSolutionPower_bound (parameter : ℝ) (order : ℕ) (source : apGrade 1 0 0 1 1 order) :
    ‖angularWeakSolutionPower parameter order source‖ ≤ (2 * unitRotationPowerConstant order) * ‖source‖ :=
  (firstAngularWeakSolution_bound parameter (sourceHighPower order source)).trans
    ((mul_le_mul_of_nonneg_left (sourceHighPower_bound order source) (by norm_num)).trans_eq (mul_assoc _ _ _).symm)

theorem angularWeakSolutionPower_mode (parameter : ℝ) (order : ℕ) (source : apGrade 1 0 0 1 1 order) (mode : ℤ) :
    highDiskMode mode (angularWeakSolutionPower parameter order source) =
      (Complex.I * (mode : ℂ)) ^ (order + 1) • highDiskMode mode
        (highRobinWeakInverse parameter (sourceHighBulk order source)) := by
  have first := firstAngularWeakSolution_mode parameter (sourceHighPower order source) mode
  have transfer := highRobinWeakInverse_mode_transfer parameter mode ((Complex.I * (mode : ℂ)) ^ order)
    (sourceHighBulk order source) (sourceHighPower order source) (sourceHighPower_coefficient order mode source)
  exact first.trans ((congrArg (fun value : highDiskGrade => (Complex.I * (mode : ℂ)) • value) transfer).trans
    ((smul_smul _ _ _).trans (congrArg (fun scalar : ℂ => scalar • highDiskMode mode
      (highRobinWeakInverse parameter (sourceHighBulk order source))) (pow_succ' _ order).symm)))

theorem sourceHighBulk_lowering {low high : ℕ} (ordered : low ≤ high) (source : apGrade 1 0 0 1 1 high) :
    sourceHighBulk low (apLowering 1 0 0 1 ordered source) = sourceHighBulk high source :=
  congrArg highL2ProjectionInto (apL2Trace_lowering 1 0 0 1 ordered 0 source)

end Grad.CircularHighWeak
