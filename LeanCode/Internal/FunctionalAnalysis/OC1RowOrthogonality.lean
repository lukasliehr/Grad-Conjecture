import GradOrthogonalCoefficientsInterface

open Grad.PDEBootstrap

namespace Grad.OrthogonalCoefficients

theorem coefficient_eq_inverse_coordinate (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (input output : Fin 2) :
    coefficient orthogonal input output = orthogonal.symm (spatialDirection input) output := by
  have identity := orthogonal.inner_map_eq_flip
    (spatialDirection output) (spatialDirection input)
  change inner ℝ (orthogonal (spatialDirection output)) (EuclideanSpace.single input 1) =
    inner ℝ (EuclideanSpace.single output 1) (orthogonal.symm (spatialDirection input)) at identity
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, coefficient]
    using identity

theorem rowOrthogonality : RowOrthogonalityGoal := by
  intro orthogonal first second
  simp_rw [coefficient_eq_inverse_coordinate]
  calc
    ∑ output : Fin 2, orthogonal.symm (spatialDirection first) output *
        orthogonal.symm (spatialDirection second) output =
        inner ℝ (orthogonal.symm (spatialDirection first))
          (orthogonal.symm (spatialDirection second)) := by
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply]
    _ = inner ℝ (spatialDirection first) (spatialDirection second) :=
      orthogonal.symm.inner_map_map _ _
    _ = if first = second then 1 else 0 := by
      change inner ℝ (EuclideanSpace.single first 1) (EuclideanSpace.single second 1) = _
      simp [EuclideanSpace.inner_single_left, PiLp.single_apply]

end Grad.OrthogonalCoefficients
