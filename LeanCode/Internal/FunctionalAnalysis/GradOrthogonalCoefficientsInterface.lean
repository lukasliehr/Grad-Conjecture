import WeakH1

noncomputable section

open Grad.PDEBootstrap

namespace Grad.OrthogonalCoefficients

def coefficient (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (input output : Fin 2) : ℝ :=
  orthogonal (spatialDirection output) input

def RowOrthogonalityGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (first second : Fin 2),
    ∑ output : Fin 2, coefficient orthogonal first output *
      coefficient orthogonal second output = if first = second then 1 else 0

end Grad.OrthogonalCoefficients
