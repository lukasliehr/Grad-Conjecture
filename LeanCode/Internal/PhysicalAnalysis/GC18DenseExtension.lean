import GC18APProjection

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

theorem apDense_extension {C F T : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup T] [NormedSpace ℂ T] [CompleteSpace T]
    (embed : C →ₗ[ℂ] F) (injective : Function.Injective embed) (dense : DenseRange embed)
    (mapping : C →ₗ[ℂ] T) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ core, ‖mapping core‖ ≤ constant * ‖embed core‖) :
    ∃ completed : F →L[ℂ] T, (∀ core, completed (embed core) = mapping core) ∧
      (∀ field, ‖completed field‖ ≤ constant * ‖field‖) := by
  let equiv : C ≃ₗ[ℂ] LinearMap.range embed := LinearEquiv.ofInjective embed injective
  let inclusion : LinearMap.range embed →L[ℂ] F := (LinearMap.range embed).subtypeL
  have inclusionDense : DenseRange inclusion := by
    change DenseRange (Subtype.val : LinearMap.range embed → F)
    exact denseRange_subtype_val.mpr dense
  have inclusionInducing : IsUniformInducing inclusion := isometry_subtype_coe.isUniformInducing
  let coreMap : LinearMap.range embed →ₗ[ℂ] T := mapping.comp equiv.symm.toLinearMap
  have pointLaw (point : LinearMap.range embed) : (point : F) = embed (equiv.symm point) := by
    calc
      _ = ((equiv (equiv.symm point) : LinearMap.range embed) : F) := by rw [LinearEquiv.apply_symm_apply]
      _ = _ := LinearEquiv.ofInjective_apply embed _
  have coreBound (point : LinearMap.range embed) : ‖coreMap point‖ ≤ constant * ‖point‖ := by
    change ‖mapping (equiv.symm point)‖ ≤ _
    rw [← Submodule.norm_coe point, pointLaw]
    exact bound _
  let continuousCore := coreMap.mkContinuous constant coreBound
  let completed := continuousCore.extend inclusion
  refine ⟨completed, ?_, ?_⟩
  · intro core
    have law := ContinuousLinearMap.extend_eq continuousCore inclusionDense inclusionInducing (equiv core)
    have embedded : inclusion (equiv core) = embed core := LinearEquiv.ofInjective_apply (h := injective) embed core
    rw [embedded] at law
    rw [law, LinearMap.mkContinuous_apply]
    change mapping (equiv.symm (equiv core)) = mapping core
    rw [LinearEquiv.symm_apply_apply]
  · intro field
    have extended := ContinuousLinearMap.opNorm_extend_le continuousCore (N := 1) inclusionDense
      (fun point => by change ‖point‖ ≤ (1 : ℝ) * ‖(point : F)‖; simp only [one_mul, Submodule.norm_coe]; exact le_rfl)
    rw [NNReal.coe_one, one_mul] at extended
    exact (completed.le_opNorm field).trans (mul_le_mul_of_nonneg_right
      (extended.trans (LinearMap.mkContinuous_norm_le coreMap nonnegative coreBound)) (norm_nonneg _))

end Grad.GaugeCoefficients.Physical.RadialLedger
