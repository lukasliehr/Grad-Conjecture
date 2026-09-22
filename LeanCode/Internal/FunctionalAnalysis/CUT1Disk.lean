import CUT1Cover

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff Topology

namespace Grad.CompactCutoff

def diskCutoff (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius) (positiveMargin : 0 < margin) :
    Cutoff (Metric.closedBall (0 : Spatial) radius) (Metric.ball (0 : Spatial) (radius + 3 * margin)) where
  toFun := diskBump radius margin nonnegativeRadius positiveMargin
  smooth := (diskBump radius margin nonnegativeRadius positiveMargin).contDiff
  compact := (diskBump radius margin nonnegativeRadius positiveMargin).hasCompactSupport
  nonnegative := (diskBump radius margin nonnegativeRadius positiveMargin).nonneg'
  atMostOne := fun _ => (diskBump radius margin nonnegativeRadius positiveMargin).le_one
  supported := by
    rw [(diskBump radius margin nonnegativeRadius positiveMargin).tsupport_eq]
    exact Metric.closedBall_subset_ball (by change radius + 2 * margin < radius + 3 * margin; linarith)
  near := by
    refine ⟨Metric.ball (0 : Spatial) (radius + margin), Metric.isOpen_ball,
      Metric.closedBall_subset_ball (by linarith), Metric.ball_subset_ball (by linarith), ?_⟩
    intro point membership
    exact (diskBump radius margin nonnegativeRadius positiveMargin).one_of_mem_closedBall
      (Metric.ball_subset_closedBall membership)

theorem diskCutoff_support (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius)
    (positiveMargin : 0 < margin) :
    tsupport (diskCutoff radius margin nonnegativeRadius positiveMargin).toFun =
      Metric.closedBall (0 : Spatial) (radius + 2 * margin) :=
  (diskBump radius margin nonnegativeRadius positiveMargin).tsupport_eq

theorem diskCutoff_one (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius)
    (positiveMargin : 0 < margin) :
    Set.EqOn (diskCutoff radius margin nonnegativeRadius positiveMargin).toFun (fun _ => 1)
      (Metric.closedBall (0 : Spatial) (radius + margin)) :=
  fun _ membership => (diskBump radius margin nonnegativeRadius positiveMargin).one_of_mem_closedBall membership

theorem diskCutoff_germ (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius)
    (positiveMargin : 0 < margin) (point : Spatial)
    (membership : point ∈ Metric.ball (0 : Spatial) (radius + margin)) :
    (diskCutoff radius margin nonnegativeRadius positiveMargin).toFun =ᶠ[𝓝 point] (fun _ => 1) :=
  (diskBump radius margin nonnegativeRadius positiveMargin).eventuallyEq_one_of_mem_ball membership

theorem disk_consumer : DiskGoal := by
  intro radius margin nonnegativeRadius positiveMargin
  exact ⟨diskCutoff radius margin nonnegativeRadius positiveMargin, rfl,
    diskCutoff_support radius margin nonnegativeRadius positiveMargin,
    diskCutoff_one radius margin nonnegativeRadius positiveMargin,
    diskCutoff_germ radius margin nonnegativeRadius positiveMargin,
    Metric.closedBall_subset_ball (by linarith), Metric.closedBall_subset_ball (by linarith)⟩

end Grad.CompactCutoff
