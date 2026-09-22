import AKCZ6ShiftedResolventContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped Topology
namespace Grad.NashMoser.InverseCalculus
variable {Parameter Input HighState MiddleSource Output : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup HighState] [NormedSpace ℝ HighState]
    [NormedAddCommGroup MiddleSource] [NormedSpace ℝ MiddleSource]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]

def shiftedInverseDerivative (outer : MiddleSource →L[ℝ] Output)
    (derivative : Parameter →L[ℝ] (HighState →L[ℝ] MiddleSource))
    (inner : Input →L[ℝ] HighState) : Parameter →L[ℝ] (Input →L[ℝ] Output) :=
  -((ContinuousLinearMap.compL ℝ Input MiddleSource Output outer).comp
    (((ContinuousLinearMap.compL ℝ Input HighState MiddleSource).flip inner).comp derivative))

theorem shiftedInverseDerivative_apply (outer : MiddleSource →L[ℝ] Output)
    (derivative : Parameter →L[ℝ] (HighState →L[ℝ] MiddleSource))
    (inner : Input →L[ℝ] HighState) (direction : Parameter) :
    shiftedInverseDerivative outer derivative inner direction = -(outer.comp (derivative direction)).comp inner := rfl

/-- A continuous outer inverse and a differentiable forward map give the
actual shifted inverse derivative. Differentiability of the outer inverse is
not a hypothesis. -/
theorem shifted_resolvent_hasFDerivAt
    (low : Parameter → Input →L[ℝ] Output)
    (outer : Parameter → MiddleSource →L[ℝ] Output)
    (forward : Parameter → HighState →L[ℝ] MiddleSource)
    (inner : Input →L[ℝ] HighState) (base : Parameter)
    (resolvent : ∀ᶠ point in 𝓝 base,
      low point-low base = -(outer point).comp ((forward point-forward base).comp inner))
    (continuous : ContinuousAt outer base)
    (derivative : Parameter →L[ℝ] (HighState →L[ℝ] MiddleSource))
    (differentiable : HasFDerivAt forward derivative base) :
    HasFDerivAt low (shiftedInverseDerivative (outer base) derivative inner) base := by
  let remainder := fun point => forward point-forward base-derivative (point-base)
  let factor := fun point => ‖outer point-outer base‖*‖derivative‖*‖inner‖ +
    (‖outer point‖*‖inner‖)*(‖point-base‖⁻¹*‖remainder point‖)
  have remLimit : Tendsto (fun point => ‖point-base‖⁻¹*‖remainder point‖) (𝓝 base) (𝓝 0) :=
    hasFDerivAt_iff_tendsto.mp differentiable
  have factorLimit : Tendsto factor (𝓝 base) (𝓝 0) := by
    simpa only [factor,sub_self,norm_zero,zero_mul,mul_zero,add_zero] using
      (((continuous.tendsto.sub_const (outer base)).norm.mul_const ‖derivative‖).mul_const ‖inner‖).add
        ((continuous.tendsto.norm.mul_const ‖inner‖).mul remLimit)
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro epsilon positive
  have small := factorLimit.eventually (gt_mem_nhds positive)
  filter_upwards [resolvent,small] with point same small
  by_cases equal : point=base
  · subst point
    simp
  have nonzero : ‖point-base‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr equal)
  have algebra : low point-low base-shiftedInverseDerivative (outer base) derivative inner (point-base) =
      -((outer point-outer base).comp (derivative (point-base))).comp inner -
        (outer point).comp ((remainder point).comp inner) := by
    rw [same,shiftedInverseDerivative_apply]
    apply ContinuousLinearMap.ext
    intro source
    simp only [remainder,ContinuousLinearMap.comp_apply,sub_apply,neg_apply,map_sub]
    abel
  have firstBound : ‖((outer point-outer base).comp (derivative (point-base))).comp inner‖ ≤
      ‖outer point-outer base‖*‖derivative‖*‖point-base‖*‖inner‖ := by
    calc
      _ ≤ (‖outer point-outer base‖*‖derivative (point-base)‖)*‖inner‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ _ := by
        have bounded := derivative.le_opNorm (point-base)
        nlinarith only [mul_le_mul_of_nonneg_left bounded (norm_nonneg (outer point-outer base)),
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bounded (norm_nonneg (outer point-outer base))) (norm_nonneg inner)]
  have secondBound : ‖(outer point).comp ((remainder point).comp inner)‖ ≤
      ‖outer point‖*(‖remainder point‖*‖inner‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  calc
    _ ≤ ‖((outer point-outer base).comp (derivative (point-base))).comp inner‖ +
        ‖(outer point).comp ((remainder point).comp inner)‖ := by rw [algebra]; exact (norm_sub_le _ _).trans (by rw [norm_neg])
    _ ≤ ‖outer point-outer base‖*‖derivative‖*‖point-base‖*‖inner‖ +
        ‖outer point‖*(‖remainder point‖*‖inner‖) := add_le_add firstBound secondBound
    _ = factor point*‖point-base‖ := by
      dsimp [factor]
      field_simp [nonzero]
    _ ≤ epsilon*‖point-base‖ := mul_le_mul_of_nonneg_right small.le (norm_nonneg _)

end Grad.NashMoser.InverseCalculus
