import AKDL7ClosedCylinderAmbientJets
import QO17ScalarMean
import RotationAverageAlgebra

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Radial

/-- A literal vanishing mean-removed row is constant on every original
rotation orbit. No potential gauge or mean-zero premise is used. -/
theorem projected_zero_rotation_invariant (field : Plane → ℝ → ℝ)
    (time : ℝ) (zero : ∀ point : Plane, ‖point‖ ≤ 1 → removeAngularAverage field point time = 0)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (angle : ℝ) :
    field (planeRotationAction angle point) time = field point time := by
  have atPoint := zero point pointIn
  have atRotation := zero (planeRotationAction angle point) (by simpa using pointIn)
  unfold removeAngularAverage at atPoint atRotation
  rw [angularAverage_eq_rotationAverage, rotationAverage_rotation] at atRotation
  rw [angularAverage_eq_rotationAverage] at atPoint
  linarith

/-- The angular derivative of each actual unprojected row is zero when
its mean-removed equation holds on the closed disk. -/
theorem projected_zero_diskAngular (field : Plane → ℝ → ℝ)
    (time : ℝ) (zero : ∀ point : Plane, ‖point‖ ≤ 1 → removeAngularAverage field point time = 0)
    (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (differentiable : DifferentiableAt ℝ (fun argument => field argument time) point) :
    diskAngular field point time = 0 := by
  have rotationAtZero : planeRotationAction 0 point = point := by
    ext coordinate
    fin_cases coordinate <;> simp [planeRotationAction, Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail]
  have outer : DifferentiableAt ℝ (fun argument => field argument time) (planeRotationAction 0 point) :=
    rotationAtZero.symm ▸ differentiable
  have derivative := outer.hasFDerivAt.comp_hasDerivAt 0
    (planeRotationAction_hasDerivAt point 0)
  have identity : (fun angle : ℝ => field (planeRotationAction angle point) time) =
      fun _ : ℝ => field point time := by
    funext angle
    exact projected_zero_rotation_invariant field time zero point pointIn angle
  rw [rotationAtZero] at derivative
  change HasDerivAt (fun angle : ℝ => field (planeRotationAction angle point) time)
    (diskAngular field point time) 0 at derivative
  rw [identity] at derivative
  exact derivative.unique (hasDerivAt_const 0 (field point time))

end Grad.PhysicalEquilibrium
