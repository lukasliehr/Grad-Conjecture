import TensorLiftProof

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays Grad.KernelPullback

namespace Grad.TensorLift

theorem tensorLift_literal_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    tensorLift rank orthogonal field = WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
      ∑ input : Fin rank → Fin 2,
        (∏ position : Fin rank,
          orthogonal (spatialDirection (output position)) (input position)) •
            orthogonalPullback orthogonal (field input)) := rfl

theorem tensorLift_literal_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    (tensorLift rank orthogonal).symm field = WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
      ∑ input : Fin rank → Fin 2,
        (∏ position : Fin rank,
          orthogonal.symm (spatialDirection (output position)) (input position)) •
            orthogonalPullback orthogonal.symm (field input)) :=
  tensorLift_symm_apply rank orthogonal field

theorem literalConsumer : literalConsumerGoal := by
  intro rank orthogonal
  exact ⟨tensorLift rank orthogonal, tensorLift_literal_apply rank orthogonal,
    tensorLift_literal_symm_apply rank orthogonal⟩

end Grad.TensorLift
