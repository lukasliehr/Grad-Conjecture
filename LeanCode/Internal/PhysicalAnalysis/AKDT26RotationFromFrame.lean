import AKDT25PreservedNormalShape

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalEquilibrium
open Grad.MainAssembly.CircleIsometryClassification Grad.MainAssembly.SampledAxisBasics

/-- The three actual axis-frame vectors determine the whole ambient rotation. -/
theorem orthogonal_eq_rotation_of_axis_frame (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (shift : ℝ)
    (radial : orthogonal (axisRadial 0) = axisRadial shift)
    (tangent : orthogonal (axisTangent 0) = axisTangent shift)
    (vertical : orthogonal axisVertical = axisVertical) :
    ∀ point : Vec, orthogonal point = rotation shift point := by
  have basisSame (coordinate : Fin 3) : orthogonal (basisVector coordinate) = rotation shift (basisVector coordinate) := by
    fin_cases coordinate
    · have source : axisRadial 0 = basisVector 0 := by ext coordinate; fin_cases coordinate <;> simp [axisRadial, basisVector, vector]
      have target : axisRadial shift = rotation shift (basisVector 0) := by ext coordinate; fin_cases coordinate <;> simp [axisRadial, basisVector, rotation, vector]
      rwa [source, target] at radial
    · have source : axisTangent 0 = basisVector 1 := by ext coordinate; fin_cases coordinate <;> simp [axisTangent, basisVector, vector]
      have target : axisTangent shift = rotation shift (basisVector 1) := by ext coordinate; fin_cases coordinate <;> simp [axisTangent, basisVector, rotation, vector]
      rwa [source, target] at tangent
    · have source : axisVertical = basisVector 2 := by ext coordinate; fin_cases coordinate <;> simp [axisVertical, basisVector, vector]
      have target : rotation shift (basisVector 2) = basisVector 2 := by ext coordinate; fin_cases coordinate <;> simp [rotation, basisVector, vector]
      change orthogonal (basisVector 2) = rotation shift (basisVector 2)
      rw [target]
      rwa [source] at vertical
  intro point
  change orthogonal.toContinuousLinearMap point = rotationCLM shift point
  rw [vec_basis_decomposition point, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [map_smul, map_smul]
  exact congrArg (fun value : Vec => point coordinate • value) (basisSame coordinate)

end Grad.PhysicalGeometry
