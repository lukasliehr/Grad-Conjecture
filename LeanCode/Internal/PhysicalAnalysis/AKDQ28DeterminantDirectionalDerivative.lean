import AKDQ27DeterminantTraceAlgebra

noncomputable section
set_option maxHeartbeats 1600000
open Set

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledFullGeometry

theorem diskAngular_tripleDeterminant (first second third : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (fun argument => first argument time) point)
    (secondDiff : DifferentiableAt ℝ (fun argument => second argument time) point)
    (thirdDiff : DifferentiableAt ℝ (fun argument => third argument time) point) :
    diskAngular (fun argument cell => tripleDeterminant (first argument cell) (second argument cell) (third argument cell))
      point time =
      tripleDeterminant (diskAngular first point time) (second point time) (third point time) +
      tripleDeterminant (first point time) (diskAngular second point time) (third point time) +
      tripleDeterminant (first point time) (second point time) (diskAngular third point time) := by
  have firstCoordinates (coordinate : Fin 3) :=
    (vecCoordinateCLM coordinate).hasFDerivAt.comp point firstDiff.hasFDerivAt
  have secondCoordinates (coordinate : Fin 3) :=
    (vecCoordinateCLM coordinate).hasFDerivAt.comp point secondDiff.hasFDerivAt
  have thirdCoordinates (coordinate : Fin 3) :=
    (vecCoordinateCLM coordinate).hasFDerivAt.comp point thirdDiff.hasFDerivAt
  have term (a b c : Fin 3) := ((firstCoordinates a).mul (secondCoordinates b)).mul (thirdCoordinates c)
  have derivative := (((((term 0 1 2).sub (term 0 2 1)).sub (term 1 0 2)).add (term 1 2 0)).add (term 2 0 1)).sub (term 2 1 0)
  have expression : (fun argument : Plane => tripleDeterminant (first argument time) (second argument time) (third argument time)) =
      fun argument => first argument time 0 * second argument time 1 * third argument time 2 -
        first argument time 0 * second argument time 2 * third argument time 1 -
        first argument time 1 * second argument time 0 * third argument time 2 +
        first argument time 1 * second argument time 2 * third argument time 0 +
        first argument time 2 * second argument time 0 * third argument time 1 -
        first argument time 2 * second argument time 1 * third argument time 0 := by
    funext argument
    exact tripleDeterminant_eq _ _ _
  have value := congrArg (fun linear : Plane →L[ℝ] ℝ => linear (planeQuarterTurn point)) derivative.fderiv
  change fderiv ℝ (fun argument : Plane => first argument time 0 * second argument time 1 * third argument time 2 -
        first argument time 0 * second argument time 2 * third argument time 1 -
        first argument time 1 * second argument time 0 * third argument time 2 +
        first argument time 1 * second argument time 2 * third argument time 0 +
        first argument time 2 * second argument time 0 * third argument time 1 -
        first argument time 2 * second argument time 1 * third argument time 0) point (planeQuarterTurn point) = _ at value
  rw [← expression] at value
  change diskAngular (fun argument cell => tripleDeterminant (first argument cell) (second argument cell) (third argument cell))
      point time = _ at value
  rw [value]
  simp [tripleDeterminant_eq, diskAngular]
  ring

end Grad.PhysicalEquilibrium
