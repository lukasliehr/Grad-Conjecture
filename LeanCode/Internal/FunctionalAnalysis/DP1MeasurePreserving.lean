import DP1DomainInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.KernelPullback.Domain

theorem invariant_refl (domain : Set Spatial) :
    Invariant domain (LinearIsometryEquiv.refl ℝ Spatial) := by
  intro point
  rfl

theorem invariant_symm (domain : Set Spatial) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Invariant domain orthogonal) : Invariant domain orthogonal.symm := by
  intro point
  simpa only [orthogonal.apply_symm_apply] using (invariant (orthogonal.symm point)).symm

theorem invariant_trans (domain : Set Spatial) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (firstInvariant : Invariant domain first) (secondInvariant : Invariant domain second) :
    Invariant domain (first.trans second) := by
  intro point
  exact (secondInvariant (first point)).trans (firstInvariant point)

theorem domainMeasurePreserving (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal) :
    MeasurePreserving orthogonal ((volume : Measure Spatial).restrict domain)
      ((volume : Measure Spatial).restrict domain) := by
  have preimage : orthogonal ⁻¹' domain = domain := Set.ext invariant
  simpa only [preimage] using orthogonal.measurePreserving.restrict_preimage measurable

end Grad.KernelPullback.Domain
