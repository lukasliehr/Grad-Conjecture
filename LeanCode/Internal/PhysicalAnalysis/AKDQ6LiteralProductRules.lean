import AKDQ5AxialCommutation

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem spatial_fderiv_eq_on_closedDisk (first second : Plane → Value)
    (agrees : EqOn first second (Metric.closedBall 0 1))
    (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (firstDiff : DifferentiableAt ℝ first point) (secondDiff : DifferentiableAt ℝ second point) :
    fderiv ℝ first point = fderiv ℝ second point := by
  have membership : point ∈ Metric.closedBall (0 : Plane) 1 := by simpa using pointIn
  have unique : UniqueDiffWithinAt ℝ (Metric.closedBall (0 : Plane) 1) point :=
    uniqueDiffWithinAt_convex (convex_closedBall (0 : Plane) 1)
      ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩ (subset_closure membership)
  have equality := fderivWithin_congr' (𝕜 := ℝ) agrees membership
  rwa [fderivWithin_eq_fderiv unique firstDiff, fderivWithin_eq_fderiv unique secondDiff] at equality

theorem diskAngular_sub (first second : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (fun argument => first argument time) point)
    (secondDiff : DifferentiableAt ℝ (fun argument => second argument time) point) :
    diskAngular (fun argument cell => first argument cell - second argument cell) point time =
      diskAngular first point time - diskAngular second point time := by
  unfold diskAngular
  exact congrArg (fun derivative => derivative (planeQuarterTurn point))
    (firstDiff.hasFDerivAt.sub secondDiff.hasFDerivAt).fderiv

theorem diskEuler_sub (first second : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (fun argument => first argument time) point)
    (secondDiff : DifferentiableAt ℝ (fun argument => second argument time) point) :
    diskEuler (fun argument cell => first argument cell - second argument cell) point time =
      diskEuler first point time - diskEuler second point time := by
  unfold diskEuler
  exact congrArg (fun derivative => derivative point)
    (firstDiff.hasFDerivAt.sub secondDiff.hasFDerivAt).fderiv

theorem cellDerivative_sub (first second : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (first point) time)
    (secondDiff : DifferentiableAt ℝ (second point) time) :
    cellDerivative (fun argument cell => first argument cell - second argument cell) point time =
      cellDerivative first point time - cellDerivative second point time := by
  unfold cellDerivative
  exact congrArg (fun derivative => derivative 1)
    (firstDiff.hasFDerivAt.sub secondDiff.hasFDerivAt).fderiv

theorem diskAngular_inner (first second : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (fun argument => first argument time) point)
    (secondDiff : DifferentiableAt ℝ (fun argument => second argument time) point) :
    diskAngular (fun argument cell => inner ℝ (first argument cell) (second argument cell)) point time =
      inner ℝ (first point time) (diskAngular second point time) +
        inner ℝ (diskAngular first point time) (second point time) :=
  fderiv_inner_apply ℝ firstDiff secondDiff (planeQuarterTurn point)

theorem diskEuler_inner (first second : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (fun argument => first argument time) point)
    (secondDiff : DifferentiableAt ℝ (fun argument => second argument time) point) :
    diskEuler (fun argument cell => inner ℝ (first argument cell) (second argument cell)) point time =
      inner ℝ (first point time) (diskEuler second point time) +
        inner ℝ (diskEuler first point time) (second point time) :=
  fderiv_inner_apply ℝ firstDiff secondDiff point

theorem cellDerivative_inner (first second : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (firstDiff : DifferentiableAt ℝ (first point) time)
    (secondDiff : DifferentiableAt ℝ (second point) time) :
    cellDerivative (fun argument cell => inner ℝ (first argument cell) (second argument cell)) point time =
      inner ℝ (first point time) (cellDerivative second point time) +
        inner ℝ (cellDerivative first point time) (second point time) :=
  fderiv_inner_apply ℝ firstDiff secondDiff 1

theorem diskEuler_norm_sq (field : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (fun argument => field argument time) point) :
    diskEuler (fun argument cell => ‖field argument cell‖ ^ 2) point time =
      2 * inner ℝ (field point time) (diskEuler field point time) := by
  have identity : (fun argument cell => ‖field argument cell‖ ^ 2) =
      fun argument cell => inner ℝ (field argument cell) (field argument cell) := by
    funext argument cell
    exact (real_inner_self_eq_norm_sq _).symm
  rw [identity, diskEuler_inner field field point time differentiable differentiable, real_inner_comm]
  ring

theorem cellDerivative_norm_sq (field : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (field point) time) :
    cellDerivative (fun argument cell => ‖field argument cell‖ ^ 2) point time =
      2 * inner ℝ (field point time) (cellDerivative field point time) := by
  have identity : (fun argument cell => ‖field argument cell‖ ^ 2) =
      fun argument cell => inner ℝ (field argument cell) (field argument cell) := by
    funext argument cell
    exact (real_inner_self_eq_norm_sq _).symm
  rw [identity, cellDerivative_inner field field point time differentiable differentiable, real_inner_comm]
  ring

theorem diskEuler_radius_sq (point : Plane) (time : ℝ) :
    diskEuler (fun argument _cell => ‖argument‖ ^ 2) point time = 2 * ‖point‖ ^ 2 := by
  unfold diskEuler
  rw [fderiv_norm_sq_apply]
  simp

end Grad.PhysicalEquilibrium
