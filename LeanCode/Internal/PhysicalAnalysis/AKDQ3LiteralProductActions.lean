import AKDQ2DirectionalCalculus
import SmoothRowFields

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

abbrev SpatialCell := Plane × ℝ

def eulerDirection : SpatialCell →L[ℝ] SpatialCell :=
  (ContinuousLinearMap.inl ℝ Plane ℝ).comp (ContinuousLinearMap.fst ℝ Plane ℝ)

def angularDirection : SpatialCell →L[ℝ] SpatialCell :=
  (ContinuousLinearMap.inl ℝ Plane ℝ).comp
    (quarterTurnCLM.comp (ContinuousLinearMap.fst ℝ Plane ℝ))

def axialDirection : SpatialCell := (0, 1)

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem spatialSection_fderiv (field : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (Function.uncurry field) (point, time)) :
    fderiv ℝ (fun argument => field argument time) point =
      (fderiv ℝ (Function.uncurry field) (point, time)).comp (ContinuousLinearMap.inl ℝ Plane ℝ) := by
  have insertion : HasFDerivAt (fun argument : Plane => (argument, time))
      (ContinuousLinearMap.inl ℝ Plane ℝ) point :=
    (hasFDerivAt_id point).prodMk (hasFDerivAt_const time point)
  exact (differentiable.hasFDerivAt.comp point insertion).fderiv

theorem timeSection_fderiv (field : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (Function.uncurry field) (point, time)) :
    fderiv ℝ (field point) time =
      (fderiv ℝ (Function.uncurry field) (point, time)).comp (ContinuousLinearMap.inr ℝ Plane ℝ) := by
  have insertion : HasFDerivAt (fun argument : ℝ => (point, argument))
      (ContinuousLinearMap.inr ℝ Plane ℝ) time :=
    (hasFDerivAt_const point time).prodMk (hasFDerivAt_id time)
  exact (differentiable.hasFDerivAt.comp time insertion).fderiv

theorem diskEuler_eq_directionalAction (field : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (Function.uncurry field) (point, time)) :
    diskEuler field point time = directionalAction (Function.uncurry field) eulerDirection (point, time) := by
  unfold diskEuler
  rw [spatialSection_fderiv field point time differentiable]
  rfl

theorem diskAngular_eq_directionalAction (field : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (Function.uncurry field) (point, time)) :
    diskAngular field point time = directionalAction (Function.uncurry field) angularDirection (point, time) := by
  unfold diskAngular
  rw [spatialSection_fderiv field point time differentiable]
  rfl

theorem cellDerivative_eq_directionalAction (field : Plane → ℝ → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (Function.uncurry field) (point, time)) :
    cellDerivative field point time =
      directionalAction (Function.uncurry field) (fun _ => axialDirection) (point, time) := by
  unfold cellDerivative
  rw [timeSection_fderiv field point time differentiable]
  rfl

/-- Derivative locality on the same open physical collar. -/
theorem directionalAction_congr (first second : SpatialCell → Value)
    (direction : SpatialCell → SpatialCell) (domain : Set SpatialCell) (domainOpen : IsOpen domain)
    (agrees : EqOn first second domain) (point : SpatialCell) (pointIn : point ∈ domain) :
    directionalAction first direction point = directionalAction second direction point := by
  have locallyEqual : first =ᶠ[nhds point] second :=
    Filter.mem_of_superset (domainOpen.mem_nhds pointIn) agrees
  rw [directionalAction, directionalAction, locallyEqual.fderiv_eq]

end Grad.PhysicalEquilibrium
