import TensorLinearMap

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Composition

def actionCompositionGoal : Prop :=
  ∀ (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    covectorMixing rank (first.trans second) field =
      covectorMixing rank first (covectorMixing rank second field)

def linearConsumerGoal : Prop :=
  ∀ (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial),
    Linear.covectorLinear rank (first.trans second) =
      (Linear.covectorLinear rank first).comp (Linear.covectorLinear rank second)

#check actionCompositionGoal
#check linearConsumerGoal
#check Finset.sum_comm
#check Finset.sum_smul
#check Finset.smul_sum
#check mul_smul
#check LinearMap.ext

end Grad.TensorAction.Composition
