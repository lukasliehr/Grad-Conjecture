import TensorActionInterface
import MixingNorm
import TensorCoefficientsProof
import OC1RowOrthogonality

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction

theorem covectorMixing_norm_sq (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : ‖covectorMixing rank orthogonal field‖ ^ 2 = ‖field‖ ^ 2 := by
  apply HilbertMixing.norm_sq
  intro first second
  exact TensorCoefficients.tensorCoefficient_orthogonality rank
    (OrthogonalCoefficients.coefficient orthogonal)
    (OrthogonalCoefficients.rowOrthogonality orthogonal) first second

theorem covectorMixing_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : ‖covectorMixing rank orthogonal field‖ = ‖field‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (covectorMixing_norm_sq rank orthogonal field)

end Grad.TensorAction
