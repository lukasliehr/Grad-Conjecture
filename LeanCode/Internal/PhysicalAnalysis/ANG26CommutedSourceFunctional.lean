import ANG25L2ModeConvergence
import ANG22HigherModeEstimates

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped Topology
namespace Grad.CircularHighWeak
open Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem robinValue_continuous_field (parameter : ℝ) (test : highDiskGrade) :
    Continuous (fun field : highDiskGrade => robinValue parameter field test) := by
  unfold robinValue
  exact (((continuous_const.inner highGradX.continuous).add (continuous_const.inner highGradY.continuous)).add
    (continuous_const.mul (continuous_const.inner (diskB.continuous.comp highDiskBulk.continuous)))).add
    (continuous_const.mul (continuous_const.inner robinTrace.continuous))

/-- The complete AN20 first source functional, with genuine R(test) and no
remaining angular truncation or test regularity beyond actual H1. -/
theorem firstAngularWeakSolution_functional (parameter : ℝ) (source : highDiskL2) (test : highDiskGrade) :
    robinValue parameter (firstAngularWeakSolution parameter source) test =
      -inner ℂ (highRotation test) source.val := by
  have left := ((robinValue_continuous_field parameter test).tendsto _).comp
    (finiteAngularSolution_tendsto parameter source)
  have pairing : Continuous (fun value : DiskL2 1 => -inner ℂ value source.val) :=
    (continuous_id.inner continuous_const).neg
  have right := (pairing.tendsto _).comp (diskSelectedModes_tendsto (highRotation test))
  have equal (modes : Finset ℤ) :
      robinValue parameter (highFiniteRotation modes (highRobinWeakInverse parameter source)) test =
        -inner ℂ (diskSelectedModes modes (highRotation test)) source.val :=
    (highRobinWeakInverse_first_functional parameter modes source test).trans
      (congrArg (fun value : DiskL2 1 => -inner ℂ value source.val) (highFiniteRotation_bulk modes test))
  exact tendsto_nhds_unique left (right.congr' (Filter.Eventually.of_forall (fun modes => (equal modes).symm)))

theorem angularWeakSolutionPower_functional (parameter : ℝ) (order : ℕ)
    (source : apGrade 1 0 0 1 1 order) (test : highDiskGrade) :
    robinValue parameter (angularWeakSolutionPower parameter order source) test =
      -inner ℂ (highRotation test) (sourceHighPower order source).val :=
  firstAngularWeakSolution_functional parameter (sourceHighPower order source) test

end Grad.CircularHighWeak
