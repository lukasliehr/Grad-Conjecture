import TensorPullbackInterface

open Grad.PDEBootstrap Grad.KernelArrays Grad.KernelPullback

namespace Grad.TensorAction.Pullback

theorem entrywisePullback_covectorMixing : commutationGoal := by
  intro rank spatial covector field
  apply PiLp.ext
  intro output
  change orthogonalPullback spatial
      (∑ input, TensorCoefficients.tensorCoefficient rank
        (OrthogonalCoefficients.coefficient covector) output input • field input) =
    ∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient covector) output input •
        orthogonalPullback spatial (field input)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input membership
  exact LinearMapClass.map_smul_of_tower (orthogonalPullback spatial) _ (field input)

theorem linearCommutation : linearCommutationGoal := by
  intro rank spatial covector
  apply LinearMap.ext
  intro field
  exact entrywisePullback_covectorMixing rank spatial covector field

end Grad.TensorAction.Pullback
