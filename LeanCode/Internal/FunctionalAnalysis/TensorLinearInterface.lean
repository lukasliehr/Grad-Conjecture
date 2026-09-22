import TensorActionInterface

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Linear

def addGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (first second : OrderedFields rank),
    covectorMixing rank orthogonal (first + second) =
      covectorMixing rank orthogonal first + covectorMixing rank orthogonal second

def smulGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (scalar : ℂ) (field : OrderedFields rank),
    covectorMixing rank orthogonal (scalar • field) = scalar • covectorMixing rank orthogonal field

def constructorGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    ∃ linear : OrderedFields rank →ₗ[ℂ] OrderedFields rank,
      ∀ field, linear field = covectorMixing rank orthogonal field

#check addGoal
#check smulGoal
#check constructorGoal
#check PiLp.ext
#check smul_add
#check Finset.sum_add_distrib
#check Finset.smul_sum
#check smul_comm
#synth SMulCommClass ℝ ℂ FieldL2

end Grad.TensorAction.Linear
