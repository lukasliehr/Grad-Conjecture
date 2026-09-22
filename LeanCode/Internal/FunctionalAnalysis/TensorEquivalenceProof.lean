import TensorEquivalenceInterface
import TensorIdentityProof

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays
open scoped BigOperators

namespace Grad.TensorAction.Equivalence

theorem covectorMixing_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    covectorMixing rank orthogonal.symm (covectorMixing rank orthogonal field) = field := by
  rw [← Composition.covectorMixing_trans, LinearIsometryEquiv.symm_trans_self]
  exact Identity.covectorMixing_refl rank field

theorem covectorMixing_apply_symm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    covectorMixing rank orthogonal (covectorMixing rank orthogonal.symm field) = field := by
  rw [← Composition.covectorMixing_trans, LinearIsometryEquiv.self_trans_symm]
  exact Identity.covectorMixing_refl rank field

def covectorEquiv (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank where
  toLinearEquiv :=
    { Linear.covectorLinear rank orthogonal with
      invFun := covectorMixing rank orthogonal.symm
      left_inv := covectorMixing_symm_apply rank orthogonal
      right_inv := covectorMixing_apply_symm rank orthogonal }
  norm_map' := covectorMixing_norm rank orthogonal

theorem covectorEquiv_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    covectorEquiv rank orthogonal field = covectorMixing rank orthogonal field := rfl

theorem covectorEquiv_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    (covectorEquiv rank orthogonal).symm field = covectorMixing rank orthogonal.symm field := rfl

theorem covectorEquiv_toLinearMap (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (covectorEquiv rank orthogonal).toLinearEquiv.toLinearMap =
      Linear.covectorLinear rank orthogonal := rfl

theorem covectorEquiv_toLinearMap_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    (covectorEquiv rank orthogonal).toLinearEquiv.toLinearMap field =
      Linear.covectorLinear rank orthogonal field := rfl

theorem covectorEquiv_literal_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    covectorEquiv rank orthogonal field =
      WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
        ∑ input : Fin rank → Fin 2,
          (∏ position : Fin rank,
            orthogonal (spatialDirection (output position)) (input position)) • field input) := rfl

theorem covectorEquiv_literal_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    (covectorEquiv rank orthogonal).symm field =
      WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
        ∑ input : Fin rank → Fin 2,
          (∏ position : Fin rank,
            orthogonal.symm (spatialDirection (output position)) (input position)) • field input) := rfl

theorem covectorEquiv_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial) :
    covectorEquiv rank (first.trans second) =
      (covectorEquiv rank second).trans (covectorEquiv rank first) := by
  apply LinearIsometryEquiv.ext
  intro field
  exact Composition.covectorMixing_trans rank first second field

end Grad.TensorAction.Equivalence
