import AXJ4Coordinates

noncomputable section

namespace Grad.ChartAxisProjections

variable {X Y D : Type*} [AddCommMonoid X] [Module ℝ X]
  [AddCommMonoid Y] [Module ℝ Y] [AddCommMonoid D] [Module ℝ D]

theorem splitting_forward_coordinates (extraction : X →ₗ[ℝ] D)
    (sourceExtraction : Y →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X) (sourceLift : D →ₗ[ℝ] Y)
    (forward : X →ₗ[ℝ] Y)
    (rightInverse : ∀ d, extraction (lift d) = d)
    (sourceRightInverse : ∀ d, sourceExtraction (sourceLift d) = d)
    (commutes : ∀ x, sourceExtraction (forward x) = extraction x)
    (liftLaw : ∀ d, sourceLift d = forward (lift d))
    (data : D × LinearMap.ker extraction) :
    let sourceCoordinates := splittingCoordinates sourceExtraction sourceLift sourceRightInverse
    let image := sourceCoordinates (forward ((splittingCoordinates extraction lift rightInverse).symm data))
    (image.1, image.2.val) = (data.1, forward data.2.val) := by
  dsimp only
  have extracted : sourceExtraction (forward (lift data.1 + data.2.val)) = data.1 := by
    rw [commutes, map_add, rightInverse,
      show extraction data.2.val = 0 from data.2.property, add_zero]
  apply Prod.ext
  · exact extracted
  · change forward (lift data.1 + data.2.val) +
      (-1 : ℝ) • sourceLift (sourceExtraction (forward (lift data.1 + data.2.val))) =
      forward data.2.val
    rw [extracted, liftLaw, map_add, add_right_comm, module_cancel, zero_add]

theorem splitting_forward_coordinates_subtype (extraction : X →ₗ[ℝ] D)
    (sourceExtraction : Y →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X) (sourceLift : D →ₗ[ℝ] Y)
    (forward : X →ₗ[ℝ] Y)
    (rightInverse : ∀ d, extraction (lift d) = d)
    (sourceRightInverse : ∀ d, sourceExtraction (sourceLift d) = d)
    (commutes : ∀ x, sourceExtraction (forward x) = extraction x)
    (liftLaw : ∀ d, sourceLift d = forward (lift d))
    (flatForward : LinearMap.ker extraction → LinearMap.ker sourceExtraction)
    (flatLaw : ∀ d, (flatForward d).val = forward d.val)
    (data : D × LinearMap.ker extraction) :
    splittingCoordinates sourceExtraction sourceLift sourceRightInverse
      (forward ((splittingCoordinates extraction lift rightInverse).symm data)) =
      (data.1, flatForward data.2) := by
  have block := splitting_forward_coordinates extraction sourceExtraction lift sourceLift forward
    rightInverse sourceRightInverse commutes liftLaw data
  dsimp only at block
  apply Prod.ext
  · exact congrArg (fun pair : D × Y => pair.1) block
  · apply Subtype.ext
    rw [flatLaw]
    exact congrArg (fun pair : D × Y => pair.2) block

end Grad.ChartAxisProjections
