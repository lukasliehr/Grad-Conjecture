import AKBT25ActualOriginalNativeH1
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualScaledNativeCoefficients
open Grad.CartesianStartup Grad.CartesianState Grad.ClosedJets Grad.PDEBootstrap Grad.GaugeCoefficients.Envelope
run_cmd do IO.eprintln "BEFORE_RADIUS"
/-- One radius chosen before the state, source, grade and native unknown. -/
def probeMinimalRadius (parameters : PhaseParameters) (length compact : ℝ)
    (positive : 0 < length) (nonnegative : 0 ≤ compact)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (supported : HasCompactSupport outer)
    (inside : tsupport outer ⊆ openUnitDisk) : ℝ :=
  Classical.choose (actualOriginalB10NativeGaugeResolvent parameters length compact 1 1 positive nonnegative
    zero_lt_one zero_lt_one outer smooth supported inside)

run_cmd do IO.eprintln "BEFORE_POSITIVE"
theorem probeMinimalRadius_positive (parameters : PhaseParameters) (length compact : ℝ)
    (positive : 0 < length) (nonnegative : 0 ≤ compact)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (supported : HasCompactSupport outer)
    (inside : tsupport outer ⊆ openUnitDisk) :
    0 < probeMinimalRadius parameters length compact positive nonnegative outer smooth supported inside :=
  (Classical.choose_spec (actualOriginalB10NativeGaugeResolvent parameters length compact 1 1 positive nonnegative
    zero_lt_one zero_lt_one outer smooth supported inside)).1

run_cmd do IO.eprintln "BEFORE_ADMISSIBLE"
theorem probeMinimalScale (parameters : PhaseParameters) (length : ℝ) (positive : 0 < length) :
    Admissible length parameters.sigma0 parameters.gamma (originalStartupScale length positive).val := by
  refine ⟨positive,parameters.gamma_pos,parameters.gamma_lt_min,(originalStartupScale length positive).property.1,?_⟩
  change min 1 length / 4 ≤ min 1 length
  have : 0 < min 1 length := lt_min zero_lt_one positive
  linarith

run_cmd do IO.eprintln "DONE_MINIMAL"
end Grad.ActualScaledNativeCoefficients
