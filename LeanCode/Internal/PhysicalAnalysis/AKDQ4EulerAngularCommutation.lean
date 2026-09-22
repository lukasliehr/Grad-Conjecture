import AKDQ3LiteralProductActions

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/-- Joint smoothness of the actual cell derivative on the original collar. -/
theorem cellDerivative_joint_smooth {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (cellDerivative field)) (Metric.ball 0 radius ×ˢ univ) := by
  have actionSmooth := directionalAction_contDiffOn (Function.uncurry field)
    (fun _ => axialDirection) (Metric.ball 0 radius ×ˢ univ)
    (Metric.isOpen_ball.prod isOpen_univ) smooth contDiffOn_const
  apply actionSmooth.congr
  intro point pointIn
  exact cellDerivative_eq_directionalAction field point.1 point.2
    ((smooth.contDiffAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds pointIn)).differentiableAt (by simp))

theorem eulerProduct_eqOn {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    EqOn (Function.uncurry (diskEuler field))
      (directionalAction (Function.uncurry field) eulerDirection) (Metric.ball 0 radius ×ˢ univ) := by
  intro point pointIn
  exact diskEuler_eq_directionalAction field point.1 point.2
    ((smooth.contDiffAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds pointIn)).differentiableAt (by simp))

theorem angularProduct_eqOn {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    EqOn (Function.uncurry (diskAngular field))
      (directionalAction (Function.uncurry field) angularDirection) (Metric.ball 0 radius ×ˢ univ) := by
  intro point pointIn
  exact diskAngular_eq_directionalAction field point.1 point.2
    ((smooth.contDiffAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds pointIn)).differentiableAt (by simp))

theorem axialProduct_eqOn {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    EqOn (Function.uncurry (cellDerivative field))
      (directionalAction (Function.uncurry field) (fun _ => axialDirection)) (Metric.ball 0 radius ×ˢ univ) := by
  intro point pointIn
  exact cellDerivative_eq_directionalAction field point.1 point.2
    ((smooth.contDiffAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds pointIn)).differentiableAt (by simp))

/-- Literal Euler and angular derivatives commute on one original collar. -/
theorem diskAngular_diskEuler {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    diskAngular (diskEuler field) point time = diskEuler (diskAngular field) point time := by
  have productIn : (point, time) ∈ Metric.ball (0 : Plane) radius ×ˢ (univ : Set ℝ) := ⟨pointIn, mem_univ _⟩
  have neighborhood := (Metric.isOpen_ball.prod isOpen_univ).mem_nhds productIn
  rw [diskAngular_eq_directionalAction (diskEuler field) point time
    (((diskEuler_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp)),
    diskEuler_eq_directionalAction (diskAngular field) point time
    (((diskAngular_joint_smooth smooth).contDiffAt neighborhood).differentiableAt (by simp))]
  rw [directionalAction_congr _ _ angularDirection _ (Metric.isOpen_ball.prod isOpen_univ)
    (eulerProduct_eqOn smooth) _ productIn,
    directionalAction_congr _ _ eulerDirection _ (Metric.isOpen_ball.prod isOpen_univ)
    (angularProduct_eqOn smooth) _ productIn]
  apply directionalAction_commute _ _ _ _ (smooth.contDiffAt neighborhood)
    eulerDirection.differentiableAt angularDirection.differentiableAt
  rw [eulerDirection.fderiv, angularDirection.fderiv]
  rfl

end Grad.PhysicalEquilibrium
