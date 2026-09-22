import AKDQ11ActualIntegratedCellEquations

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily

theorem vec_basis_decomposition (point : Vec) :
    point = ∑ coordinate : Fin 3, point coordinate • basisVector coordinate := by
  ext coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, basisVector]

theorem linear_apply_coordinates (linear : Vec →L[ℝ] Vec) (point : Vec) (coordinate : Fin 3) :
    (linear point) coordinate = point 0 * (linear (basisVector 0)) coordinate +
      point 1 * (linear (basisVector 1)) coordinate + point 2 * (linear (basisVector 2)) coordinate := by
  conv_lhs => arg 1; rw [vec_basis_decomposition point]
  simp [Fin.sum_univ_three]

theorem inner_gradient (pressure : Vec → ℝ) (point direction : Vec) :
    inner ℝ (gradient pressure point) direction = fderiv ℝ pressure point direction := by
  conv_rhs => arg 2; rw [vec_basis_decomposition direction]
  simp [gradient, PiLp.inner_apply, Fin.sum_univ_three]

/-- The coordinate definition of curl has exactly the required force sign. -/
theorem inner_cross_curl (magnetic : Vec → Vec) (point direction : Vec) :
    inner ℝ (cross (magnetic point) (curl magnetic point)) direction =
      inner ℝ (magnetic point) (fderiv ℝ magnetic point direction) -
        inner ℝ direction (fderiv ℝ magnetic point (magnetic point)) := by
  simp [cross, curl, vector, PiLp.inner_apply, Fin.sum_univ_three]
  rw [linear_apply_coordinates (fderiv ℝ magnetic point) direction 0,
    linear_apply_coordinates (fderiv ℝ magnetic point) direction 1,
    linear_apply_coordinates (fderiv ℝ magnetic point) direction 2,
    linear_apply_coordinates (fderiv ℝ magnetic point) (magnetic point) 0,
    linear_apply_coordinates (fderiv ℝ magnetic point) (magnetic point) 1,
    linear_apply_coordinates (fderiv ℝ magnetic point) (magnetic point) 2]
  ring

theorem ambient_force_pairing (magnetic : Vec → Vec) (pressure : Vec → ℝ) (point direction : Vec) :
    inner ℝ (cross (magnetic point) (curl magnetic point) + gradient pressure point) direction =
      inner ℝ (magnetic point) (fderiv ℝ magnetic point direction) -
        inner ℝ direction (fderiv ℝ magnetic point (magnetic point)) +
          fderiv ℝ pressure point direction := by
  rw [inner_add_left, inner_cross_curl, inner_gradient]

end Grad.PhysicalEquilibrium
