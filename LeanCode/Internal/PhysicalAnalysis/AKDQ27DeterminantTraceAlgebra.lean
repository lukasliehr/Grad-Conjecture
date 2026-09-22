import AKDQ26ActualAmbientForceFields

noncomputable section
set_option maxHeartbeats 1600000
open Set

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily

theorem tripleDeterminant_smul_first (scalar : ℝ) (first second third : Vec) :
    tripleDeterminant (scalar • first) second third = scalar * tripleDeterminant first second third := by
  simp [tripleDeterminant_eq]
  ring

theorem tripleDeterminant_smul_second (scalar : ℝ) (first second third : Vec) :
    tripleDeterminant first (scalar • second) third = scalar * tripleDeterminant first second third := by
  simp [tripleDeterminant_eq]
  ring

theorem tripleDeterminant_smul_third (scalar : ℝ) (first second third : Vec) :
    tripleDeterminant first second (scalar • third) = scalar * tripleDeterminant first second third := by
  simp [tripleDeterminant_eq]
  ring

theorem tripleDeterminant_add_third (first second third fourth : Vec) :
    tripleDeterminant first second (third + fourth) =
      tripleDeterminant first second third + tripleDeterminant first second fourth := by
  simp [tripleDeterminant_eq]
  ring

theorem tripleDeterminant_rotation (time : ℝ) (first second third : Vec) :
    tripleDeterminant (rotation time first) (rotation time second) (rotation time third) =
      tripleDeterminant first second third := by
  simp [tripleDeterminant_eq, rotation, vector]
  linear_combination
    (first 0 * second 1 * third 2 - first 0 * second 2 * third 1 -
      first 1 * second 0 * third 2 + first 1 * second 2 * third 0 +
      first 2 * second 0 * third 1 - first 2 * second 1 * third 0) * Real.sin_sq_add_cos_sq time

/-- The determinant derivative in three dimensions contracts with the
literal coordinate trace. This uses no inverse-matrix convention. -/
theorem tripleDeterminant_linear_trace (linear : Vec →L[ℝ] Vec) (first second third : Vec) :
    tripleDeterminant (linear first) second third + tripleDeterminant first (linear second) third +
        tripleDeterminant first second (linear third) =
      (∑ coordinate : Fin 3, (linear (basisVector coordinate)) coordinate) *
        tripleDeterminant first second third := by
  simp only [tripleDeterminant_eq, Fin.sum_univ_three]
  rw [linear_apply_coordinates linear first 0, linear_apply_coordinates linear first 1, linear_apply_coordinates linear first 2,
    linear_apply_coordinates linear second 0, linear_apply_coordinates linear second 1, linear_apply_coordinates linear second 2,
    linear_apply_coordinates linear third 0, linear_apply_coordinates linear third 1, linear_apply_coordinates linear third 2]
  ring

end Grad.PhysicalEquilibrium
