import AKDQ4EulerAngularCommutation

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem diskAngular_cellDerivative {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    diskAngular (cellDerivative field) point time = cellDerivative (diskAngular field) point time := by
  have productIn : (point, time) ∈ Metric.ball (0 : Plane) radius ×ˢ (univ : Set ℝ) := ⟨pointIn, mem_univ _⟩
  have neighborhood := (Metric.isOpen_ball.prod isOpen_univ).mem_nhds productIn
  rw [diskAngular_eq_directionalAction (cellDerivative field) point time
    (((cellDerivative_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp)),
    cellDerivative_eq_directionalAction (diskAngular field) point time
    (((diskAngular_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp))]
  rw [directionalAction_congr _ _ angularDirection _ (Metric.isOpen_ball.prod isOpen_univ)
    (axialProduct_eqOn smooth) _ productIn,
    directionalAction_congr _ _ (fun _ => axialDirection) _ (Metric.isOpen_ball.prod isOpen_univ)
    (angularProduct_eqOn smooth) _ productIn]
  apply directionalAction_commute _ _ _ _ (smooth.contDiffAt neighborhood)
    (differentiableAt_const axialDirection) angularDirection.differentiableAt
  have constantDerivative : fderiv ℝ (fun _ : SpatialCell => axialDirection) (point, time) = 0 :=
    (hasFDerivAt_const axialDirection (point, time)).fderiv
  rw [constantDerivative, angularDirection.fderiv]
  change (0 : SpatialCell) = (quarterTurnCLM 0, 0)
  rw [map_zero]
  rfl

theorem diskEuler_cellDerivative {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    diskEuler (cellDerivative field) point time = cellDerivative (diskEuler field) point time := by
  have productIn : (point, time) ∈ Metric.ball (0 : Plane) radius ×ˢ (univ : Set ℝ) := ⟨pointIn, mem_univ _⟩
  have neighborhood := (Metric.isOpen_ball.prod isOpen_univ).mem_nhds productIn
  rw [diskEuler_eq_directionalAction (cellDerivative field) point time
    (((cellDerivative_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp)),
    cellDerivative_eq_directionalAction (diskEuler field) point time
    (((diskEuler_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp))]
  rw [directionalAction_congr _ _ eulerDirection _ (Metric.isOpen_ball.prod isOpen_univ)
    (axialProduct_eqOn smooth) _ productIn,
    directionalAction_congr _ _ (fun _ => axialDirection) _ (Metric.isOpen_ball.prod isOpen_univ)
    (eulerProduct_eqOn smooth) _ productIn]
  apply directionalAction_commute _ _ _ _ (smooth.contDiffAt neighborhood)
    (differentiableAt_const axialDirection) eulerDirection.differentiableAt
  have constantDerivative : fderiv ℝ (fun _ : SpatialCell => axialDirection) (point, time) = 0 :=
    (hasFDerivAt_const axialDirection (point, time)).fderiv
  rw [constantDerivative, eulerDirection.fderiv]
  rfl

end Grad.PhysicalEquilibrium
