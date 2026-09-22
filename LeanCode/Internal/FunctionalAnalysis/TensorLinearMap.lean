import TensorLinearInterface

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Linear

theorem covectorMixing_add (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (first second : OrderedFields rank) :
    covectorMixing rank orthogonal (first + second) =
      covectorMixing rank orthogonal first + covectorMixing rank orthogonal second := by
  apply PiLp.ext
  intro output
  change (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input • (first input + second input)) =
    (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input • first input) +
    (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input • second input)
  simp only [smul_add, Finset.sum_add_distrib]

theorem covectorMixing_smul (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (scalar : ℂ) (field : OrderedFields rank) :
    covectorMixing rank orthogonal (scalar • field) = scalar • covectorMixing rank orthogonal field := by
  apply PiLp.ext
  intro output
  change (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input • (scalar • field input)) =
    scalar • (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input • field input)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input membership
  exact smul_comm _ scalar (field input)

def covectorLinear (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    OrderedFields rank →ₗ[ℂ] OrderedFields rank where
  toFun := covectorMixing rank orthogonal
  map_add' := covectorMixing_add rank orthogonal
  map_smul' := covectorMixing_smul rank orthogonal

theorem covectorLinear_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : covectorLinear rank orthogonal field =
      covectorMixing rank orthogonal field := rfl

end Grad.TensorAction.Linear
