import TensorLinearMap
import TensorActionNorm
import TensorCompositionProof

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Equivalence

def leftInverseGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    covectorMixing rank orthogonal.symm (covectorMixing rank orthogonal field) = field

def rightInverseGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    covectorMixing rank orthogonal (covectorMixing rank orthogonal.symm field) = field

def constructorGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    ∃ equivalence : OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank,
      equivalence.toLinearEquiv.toLinearMap = Linear.covectorLinear rank orthogonal ∧
      (∀ field : OrderedFields rank, equivalence field = covectorMixing rank orthogonal field) ∧
      (∀ field : OrderedFields rank,
        equivalence.symm field = covectorMixing rank orthogonal.symm field)

end Grad.TensorAction.Equivalence
