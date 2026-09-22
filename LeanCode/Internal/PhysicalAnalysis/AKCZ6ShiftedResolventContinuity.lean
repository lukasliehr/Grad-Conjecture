import AKCZ5ShiftedCompletedResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter
open scoped Topology
namespace Grad.NashMoser.InverseCalculus
variable {Parameter Input HighState MiddleSource Output : Type*}
    [NormedAddCommGroup Parameter]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup HighState] [NormedSpace ℝ HighState]
    [NormedAddCommGroup MiddleSource] [NormedSpace ℝ MiddleSource]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- Operator-norm continuity of the shifted inverse is obtained before any
inverse derivative is used. Only a local uniform outer bound is needed. -/
theorem shifted_resolvent_continuousAt
    (low : Parameter → Input →L[ℝ] Output)
    (outer : Parameter → MiddleSource →L[ℝ] Output)
    (forward : Parameter → HighState →L[ℝ] MiddleSource)
    (inner : Input →L[ℝ] HighState) (base : Parameter)
    (resolvent : ∀ᶠ point in 𝓝 base,
      low point-low base = -(outer point).comp ((forward point-forward base).comp inner))
    (constant : ℝ) (bounded : ∀ᶠ point in 𝓝 base, ‖outer point‖ ≤ constant)
    (continuous : ContinuousAt forward base) : ContinuousAt low base := by
  have vanish : Tendsto (fun point => constant * ‖forward point-forward base‖ * ‖inner‖) (𝓝 base) (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := constant)).mul (continuous.tendsto.sub_const (forward base)).norm).mul_const ‖inner‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun point => norm_nonneg (low point-low base))) _ vanish
  filter_upwards [resolvent,bounded] with point same bound
  rw [same,norm_neg]
  calc
    ‖(outer point).comp ((forward point-forward base).comp inner)‖ ≤
        ‖outer point‖ * ‖(forward point-forward base).comp inner‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ constant * (‖forward point-forward base‖ * ‖inner‖) :=
      mul_le_mul bound (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) ((norm_nonneg _).trans bound)
    _ = _ := (mul_assoc _ _ _).symm

end Grad.NashMoser.InverseCalculus
