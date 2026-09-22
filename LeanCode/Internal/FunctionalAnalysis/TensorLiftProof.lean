import TensorLiftInterface
import TensorEquivalenceProof
import TP1PullbackCommutation

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays Grad.TensorAction

namespace Grad.TensorLift

theorem entrywisePullback_symm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (entrywisePullback rank orthogonal).symm = entrywisePullback rank orthogonal.symm := by
  apply LinearIsometryEquiv.ext
  intro field
  apply (entrywisePullback rank orthogonal).injective
  rw [LinearIsometryEquiv.apply_symm_apply, entrywisePullback_apply_symm]

def tensorLift (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank :=
  (entrywisePullback rank orthogonal).trans (Equivalence.covectorEquiv rank orthogonal)

theorem tensorLift_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    tensorLift rank orthogonal field =
      covectorMixing rank orthogonal (entrywisePullback rank orthogonal field) := rfl

theorem tensorLift_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    (tensorLift rank orthogonal).symm field =
      covectorMixing rank orthogonal.symm (entrywisePullback rank orthogonal.symm field) := by
  change (entrywisePullback rank orthogonal).symm
      ((Equivalence.covectorEquiv rank orthogonal).symm field) = _
  rw [entrywisePullback_symm, Equivalence.covectorEquiv_symm_apply]
  exact Pullback.entrywisePullback_covectorMixing rank orthogonal.symm orthogonal.symm field

theorem tensorLift_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : ‖tensorLift rank orthogonal field‖ = ‖field‖ :=
  (tensorLift rank orthogonal).norm_map field

theorem constructor : constructorGoal := by
  intro rank orthogonal
  exact ⟨tensorLift rank orthogonal, tensorLift_apply rank orthogonal,
    tensorLift_symm_apply rank orthogonal⟩

end Grad.TensorLift
