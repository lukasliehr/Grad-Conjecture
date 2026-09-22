import ACB19ActualNativeCenterGain

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak

/-- Exact AN6a/b/c consumer: one genuine smooth pinned center solution,
its literal closed-disk PDE and pure mode, and both original native bounds.
The constants precede sign, bounded real frequency, and source. -/
theorem actual_center_scalar_native_solver (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) :
    ∃ base gain : ℝ, 0 ≤ base ∧ 0 ≤ gain ∧
      ∀ (mode : ℤ), mode = 1 ∨ mode = -1 → ∀ (frequency : ℝ), |frequency| ≤ radius →
      ∀ (source : ClosedJet 1), angularClosedJet mode source = source →
      ∃! solution : ClosedJet 1,
        IsPinnedCenterSolution mode frequency source solution ∧
        ‖unitDiskCoreInto 1 solution‖ ≤ base * ‖unitDiskCoreInto 3 source‖ ∧
        ‖unitDiskCoreInto (grade + 2) solution‖ ≤ gain * ‖unitDiskCoreInto grade source‖ := by
  refine ⟨centerH1Constant radius, centerNativeGainConstant grade large radius,
    centerH1Constant_nonnegative radius, centerNativeGainConstant_nonnegative grade large radius, ?_⟩
  intro mode center frequency bounded source pure
  refine ⟨pinnedCenterSolution mode frequency source, ?_, ?_⟩
  · exact ⟨pinnedCenterSolution_specification mode center frequency source pure,
      pinnedCenterSolution_H1 radius mode center frequency bounded source pure,
      pinnedCenterSolution_native_gain grade large radius mode center frequency bounded source pure⟩
  · intro candidate specification
    exact pinnedCenterSolution_literal_unique mode center frequency source pure candidate specification.1

end Grad.ActualCenterBounds
