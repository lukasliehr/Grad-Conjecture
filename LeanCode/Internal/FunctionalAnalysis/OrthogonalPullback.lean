import WeakH1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.KernelPullback

def orthogonalPullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : FieldL2 ≃ₗᵢ[ℂ] FieldL2 where
  toFun := Lp.compMeasurePreservingₗᵢ ℂ orthogonal orthogonal.measurePreserving
  map_add' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal orthogonal.measurePreserving).map_add
  map_smul' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal orthogonal.measurePreserving).map_smul
  norm_map' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal orthogonal.measurePreserving).norm_map
  invFun := Lp.compMeasurePreserving orthogonal.symm orthogonal.symm.measurePreserving
  left_inv := by
    intro field
    change Lp.compMeasurePreserving orthogonal.symm orthogonal.symm.measurePreserving
      (Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving field) = field
    rw [← Lp.compMeasurePreserving_comp_apply]
    have composition : (⇑orthogonal ∘ ⇑orthogonal.symm : Spatial → Spatial) = id :=
      funext orthogonal.apply_symm_apply
    simpa only [composition] using Lp.compMeasurePreserving_id_apply field
  right_inv := by
    intro field
    change Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving
      (Lp.compMeasurePreserving orthogonal.symm orthogonal.symm.measurePreserving field) = field
    rw [← Lp.compMeasurePreserving_comp_apply]
    have composition : (⇑orthogonal.symm ∘ ⇑orthogonal : Spatial → Spatial) = id :=
      funext orthogonal.symm_apply_apply
    simpa only [composition] using Lp.compMeasurePreserving_id_apply field

theorem orthogonalPullback_ae (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    (orthogonalPullback orthogonal field : Spatial → CellValues) =ᵐ[volume]
      fun point => field (orthogonal point) :=
  Lp.coeFn_compMeasurePreserving field orthogonal.measurePreserving

theorem orthogonalPullback_norm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    ‖orthogonalPullback orthogonal field‖ = ‖field‖ :=
  (orthogonalPullback orthogonal).norm_map field

theorem orthogonalPullback_refl :
    orthogonalPullback (LinearIsometryEquiv.refl ℝ Spatial) =
      LinearIsometryEquiv.refl ℂ FieldL2 := by
  apply LinearIsometryEquiv.ext
  intro field
  exact Lp.compMeasurePreserving_id_apply field

theorem orthogonalPullback_trans (first second : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    orthogonalPullback (first.trans second) field =
      orthogonalPullback first (orthogonalPullback second field) :=
  Lp.compMeasurePreserving_comp_apply field second.measurePreserving first.measurePreserving

theorem orthogonalPullback_symm_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    orthogonalPullback orthogonal.symm (orthogonalPullback orthogonal field) = field :=
  (orthogonalPullback orthogonal).symm_apply_apply field

theorem orthogonalPullback_apply_symm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    orthogonalPullback orthogonal (orthogonalPullback orthogonal.symm field) = field :=
  (orthogonalPullback orthogonal).apply_symm_apply field

def orthogonalPullbackCLM (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : FieldL2 →L[ℂ] FieldL2 :=
  (orthogonalPullback orthogonal).toLinearIsometry.toContinuousLinearMap

theorem orthogonalPullbackCLM_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2) :
    orthogonalPullbackCLM orthogonal field = orthogonalPullback orthogonal field := rfl

theorem orthogonalPullbackCLM_opNorm_le (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    ‖orthogonalPullbackCLM orthogonal‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  rw [orthogonalPullbackCLM_apply, orthogonalPullback_norm, one_mul]

end Grad.KernelPullback
