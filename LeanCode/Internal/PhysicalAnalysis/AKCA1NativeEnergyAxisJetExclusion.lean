import AKBV20OriginalWidthPhysicalCoreConsumer
import AKO9CommonVanishingIncomingRadii

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.OriginalCoreRealization
open Grad.AnnularIncomingIntegrability

/-- Finite logarithmic square energy excludes a nonzero continuous limit. -/
theorem logarithmicEnergy_limit_zero (incoming : ℝ → ℝ) (measurable : Measurable incoming)
    (nonnegative : ∀ radius ∈ Ioc (0 : ℝ) 1, 0 ≤ incoming radius)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (radius⁻¹ * incoming radius ^ 2)) < ⊤)
    (limit : ℝ) (converges : Tendsto incoming (𝓝[>] (0 : ℝ)) (𝓝 limit)) : limit = 0 := by
  obtain ⟨radii,inside,_,_,_,_,radialLimit,incomingLimit⟩ :=
    exists_common_vanishing_incoming_radii 1 (by norm_num) incoming measurable nonnegative finite ∅ (by simp)
  have within : Tendsto radii atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨radialLimit,Filter.Eventually.of_forall (fun index => (inside index).1)⟩
  exact tendsto_nhds_unique (converges.comp within) incomingLimit

/-- The native radial weight excludes both the value and first derivative
of a genuinely differentiable ray, without an axis-value premise. -/
theorem logarithmicSlopeEnergy_zero_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (field : ℝ → E) (measurable : Measurable field) (derivative : E)
    (genuine : HasDerivAt field derivative 0)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (radius⁻¹ * (radius⁻¹ * ‖field radius‖) ^ 2)) < ⊤) :
    field 0 = 0 ∧ derivative = 0 := by
  let incoming := fun radius : ℝ => radius⁻¹ * ‖field radius‖
  have measurableIncoming : Measurable incoming := measurable_inv.mul measurable.norm
  have nonnegative : ∀ radius ∈ Ioc (0 : ℝ) 1, 0 ≤ incoming radius :=
    fun radius inside => mul_nonneg (inv_nonneg.mpr inside.1.le) (norm_nonneg _)
  obtain ⟨radii,inside,_,_,_,_,radialLimit,incomingLimit⟩ :=
    exists_common_vanishing_incoming_radii 1 (by norm_num) incoming measurableIncoming nonnegative finite ∅ (by simp)
  have fieldNormLimit : Tendsto (fun index => ‖field (radii index)‖) atTop (𝓝 0) := by
    have product := radialLimit.mul incomingLimit
    simpa only [incoming,Function.comp_apply,mul_zero,mul_inv_cancel_left₀ (inside _).1.ne'] using product
  have valueZero : field 0 = 0 := norm_eq_zero.mp
    (tendsto_nhds_unique (genuine.continuousAt.norm.tendsto.comp radialLimit) fieldNormLimit)
  have punctured : Tendsto radii atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨radialLimit,Filter.Eventually.of_forall (fun index => (inside index).1.ne')⟩
  have slopeLimit := (hasDerivAt_iff_tendsto_slope.mp genuine).norm.comp punctured
  have sameSlope : (fun index => ‖slope field 0 (radii index)‖) = incoming ∘ radii := by
    funext index
    simp only [slope_def_module,sub_zero,valueZero,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (inside index).1.le),incoming,Function.comp_apply]
  change Tendsto (fun index => ‖slope field 0 (radii index)‖) atTop (𝓝 ‖derivative‖) at slopeLimit
  rw [sameSlope] at slopeLimit
  exact ⟨valueZero,norm_eq_zero.mp (tendsto_nhds_unique slopeLimit incomingLimit)⟩

end Grad.OriginalCoreRealization
