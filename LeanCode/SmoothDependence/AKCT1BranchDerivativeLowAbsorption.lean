import AKCR4OriginalNewtonBranchContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter
open scoped Topology

namespace Grad.NashMoser.BranchDerivative

/-- The NM11 low-norm absorption. Only continuity-size remainders are used;
no Lipschitz or differentiability property of the branch is presumed. -/
theorem branch_low_lipschitz
    {Parameter Low : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [NormedAddCommGroup Low] [NormedSpace ℝ Low]
    (branch : Parameter → Low) (base : Parameter) (linear : Parameter →L[ℝ] Low)
    (factor : Parameter → ℝ) (vanishes : Tendsto factor (𝓝 base) (𝓝 0))
    (remainder : ∀ᶠ point in 𝓝 base,
      ‖branch point - branch base - linear (point-base)‖ ≤
        factor point * (‖point-base‖ + ‖branch point-branch base‖)) :
    ∀ᶠ point in 𝓝 base, ‖branch point-branch base‖ ≤ (2*‖linear‖+1)*‖point-base‖ := by
  have small := vanishes.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [remainder, small] with point bound small
  have split := norm_add_le (branch point-branch base-linear (point-base)) (linear (point-base))
  rw [sub_add_cancel] at split
  have paid := mul_le_mul_of_nonneg_right small.le
    (add_nonneg (norm_nonneg (point-base)) (norm_nonneg (branch point-branch base)))
  have linearBound := linear.le_opNorm (point-base)
  nlinarith

/-- A two-scale inverse remainder gives the actual Frechet derivative at
every output grade after the independently proved low absorption. This is
the quantitative implication of NM11, not differentiation of a limit series. -/
theorem branch_hasFDerivAt_of_two_scale_remainder
    {Parameter Low High : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [NormedAddCommGroup Low] [NormedSpace ℝ Low]
    [NormedAddCommGroup High] [NormedSpace ℝ High]
    (lowBranch : Parameter → Low) (branch : Parameter → High) (base : Parameter)
    (lowLinear : Parameter →L[ℝ] Low) (linear : Parameter →L[ℝ] High)
    (lowFactor factor : Parameter → ℝ)
    (lowVanishes : Tendsto lowFactor (𝓝 base) (𝓝 0))
    (vanishes : Tendsto factor (𝓝 base) (𝓝 0))
    (lowRemainder : ∀ᶠ point in 𝓝 base,
      ‖lowBranch point-lowBranch base-lowLinear (point-base)‖ ≤
        lowFactor point*(‖point-base‖+‖lowBranch point-lowBranch base‖))
    (remainder : ∀ᶠ point in 𝓝 base,
      ‖branch point-branch base-linear (point-base)‖ ≤
        factor point*(‖point-base‖+‖lowBranch point-lowBranch base‖)) :
    HasFDerivAt branch linear base := by
  have lowBound := branch_low_lipschitz lowBranch base lowLinear lowFactor lowVanishes lowRemainder
  have factorLimit : Tendsto (fun point => |factor point| *(2*‖lowLinear‖+2)) (𝓝 base) (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using vanishes.abs.mul_const (2*‖lowLinear‖+2)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro epsilon positive
  have small := factorLimit.eventually (gt_mem_nhds positive)
  filter_upwards [lowBound, remainder, small] with point lowBound bound small
  calc
    _ ≤ factor point*(‖point-base‖+‖lowBranch point-lowBranch base‖) := bound
    _ ≤ |factor point| *(‖point-base‖+‖lowBranch point-lowBranch base‖) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ |factor point| *(‖point-base‖+(2*‖lowLinear‖+1)*‖point-base‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl lowBound) (abs_nonneg _)
    _ = (|factor point| *(2*‖lowLinear‖+2))*‖point-base‖ := by ring
    _ ≤ epsilon*‖point-base‖ := mul_le_mul_of_nonneg_right small.le (norm_nonneg _)

end Grad.NashMoser.BranchDerivative
