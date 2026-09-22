import TensorLinearMap

open Grad.PDEBootstrap Grad.KernelArrays Grad.KernelPullback

namespace Grad.TensorAction.Pullback

def commutationGoal : Prop :=
  ∀ (rank : ℕ) (spatial covector : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    entrywisePullback rank spatial (covectorMixing rank covector field) =
      covectorMixing rank covector (entrywisePullback rank spatial field)

def linearCommutationGoal : Prop :=
  ∀ (rank : ℕ) (spatial covector : Spatial ≃ₗᵢ[ℝ] Spatial),
    (entrywisePullback rank spatial).toLinearEquiv.toLinearMap.comp
        (Linear.covectorLinear rank covector) =
      (Linear.covectorLinear rank covector).comp
        (entrywisePullback rank spatial).toLinearEquiv.toLinearMap

#check commutationGoal
#check linearCommutationGoal
#check PiLp.ext
#check LinearMap.ext
#check fun (spatial : Spatial ≃ₗᵢ[ℝ] Spatial) (scalar : ℝ) (field : FieldL2) =>
  LinearMapClass.map_smul_of_tower (orthogonalPullback spatial) scalar field
#check fun (rank : ℕ) (spatial : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank) =>
  map_sum (orthogonalPullback spatial) (fun word => field word) Finset.univ

end Grad.TensorAction.Pullback
