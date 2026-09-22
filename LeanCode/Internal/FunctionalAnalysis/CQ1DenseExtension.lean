import CP13Goal

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

/-! # The general dense-core bounded-idempotent extension lemma (R3 / P12)

A linear projection on a core, bounded in the completed norm through a
dense injective linear embedding, extends uniquely to a continuous linear
projection of the completion with the same bound and the exact core law. -/

theorem dense_core_projection_extension {C F : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (embed : C →ₗ[ℂ] F) (injective : Function.Injective embed) (dense : DenseRange embed)
    (core : C →ₗ[ℂ] C) (constant : ℝ) (constant_nonneg : 0 ≤ constant)
    (bound : ∀ state, ‖embed (core state)‖ ≤ constant * ‖embed state‖)
    (idempotent : ∀ state, core (core state) = core state) :
    ∃ completed : F →L[ℂ] F,
      (∀ state, completed (embed state) = embed (core state)) ∧
      (∀ point, ‖completed point‖ ≤ constant * ‖point‖) ∧
      (∀ point, completed (completed point) = completed point) ∧
      (∀ other : F →L[ℂ] F, (∀ state, other (embed state) = embed (core state)) →
        other = completed) := by
  let equiv : C ≃ₗ[ℂ] LinearMap.range embed := LinearEquiv.ofInjective embed injective
  let inclusion : LinearMap.range embed →L[ℂ] F := (LinearMap.range embed).subtypeL
  have coe_inclusion : (⇑inclusion : LinearMap.range embed → F) = Subtype.val := rfl
  have inclusionDense : DenseRange inclusion := by
    rw [coe_inclusion]
    have setEq : ({point | point ∈ LinearMap.range embed} : Set F) = Set.range embed :=
      Set.ext fun point => LinearMap.mem_range
    exact denseRange_subtype_val.mpr (setEq ▸ dense)
  have inclusionInducing : IsUniformInducing inclusion := by
    rw [coe_inclusion]
    exact isometry_subtype_coe.isUniformInducing
  let coreMap : LinearMap.range embed →ₗ[ℂ] F := (embed.comp core).comp equiv.symm.toLinearMap
  have coreMap_apply : ∀ point : LinearMap.range embed,
      coreMap point = embed (core (equiv.symm point)) := fun _ => rfl
  have pointLaw : ∀ point : LinearMap.range embed, (point : F) = embed (equiv.symm point) := by
    intro point
    calc (point : F) = ((equiv (equiv.symm point) : LinearMap.range embed) : F) := by
          rw [LinearEquiv.apply_symm_apply]
      _ = embed (equiv.symm point) := LinearEquiv.ofInjective_apply embed _
  have coreMap_bound : ∀ point : LinearMap.range embed, ‖coreMap point‖ ≤ constant * ‖point‖ := by
    intro point
    rw [coreMap_apply, ← Submodule.norm_coe point, pointLaw point]
    exact bound _
  let continuousCore : LinearMap.range embed →L[ℂ] F := coreMap.mkContinuous constant coreMap_bound
  let completed : F →L[ℂ] F := continuousCore.extend inclusion
  have coreEq : ∀ state, completed (embed state) = embed (core state) := by
    intro state
    have law := ContinuousLinearMap.extend_eq continuousCore inclusionDense inclusionInducing
      (equiv state)
    have embedded : inclusion (equiv state) = embed state := by
      rw [coe_inclusion]
      exact LinearEquiv.ofInjective_apply embed state
    rw [embedded] at law
    rw [law, LinearMap.mkContinuous_apply, coreMap_apply, LinearEquiv.symm_apply_apply]
  refine ⟨completed, coreEq, ?_, ?_, ?_⟩
  · intro point
    have normLe : ‖completed‖ ≤ constant := by
      have extended := ContinuousLinearMap.opNorm_extend_le continuousCore (N := 1) inclusionDense
        (fun point => by
          rw [coe_inclusion, Submodule.norm_coe, NNReal.coe_one, one_mul])
      rw [NNReal.coe_one, one_mul] at extended
      exact extended.trans (LinearMap.mkContinuous_norm_le coreMap constant_nonneg coreMap_bound)
    exact (completed.le_opNorm point).trans (mul_le_mul_of_nonneg_right normLe (norm_nonneg _))
  · intro point
    have agree : (fun value => completed (completed value)) ∘ embed = completed ∘ embed := by
      funext state
      simp only [Function.comp_apply]
      rw [coreEq state, coreEq (core state), idempotent]
    exact congrFun (DenseRange.equalizer dense (completed.continuous.comp completed.continuous)
      completed.continuous agree) point
  · intro other otherLaw
    have agree : (⇑other : F → F) ∘ embed = completed ∘ embed := by
      funext state
      simp only [Function.comp_apply]
      rw [otherLaw, coreEq]
    exact ContinuousLinearMap.ext fun point =>
      congrFun (DenseRange.equalizer dense other.continuous completed.continuous agree) point

end Grad.Cor18
