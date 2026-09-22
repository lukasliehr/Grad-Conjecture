import AKDQ6LiteralProductRules

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem smooth_spatial_differentiable {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    DifferentiableAt ℝ (fun argument => field argument time) point :=
  ((cellSection_smooth smooth time).contDiffAt (Metric.isOpen_ball.mem_nhds pointIn)).differentiableAt (by simp)

theorem smooth_time_differentiable {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    DifferentiableAt ℝ (field point) time := by
  have outer := (smooth.contDiffAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds
    (show (point, time) ∈ Metric.ball 0 radius ×ˢ (univ : Set ℝ) from ⟨pointIn, mem_univ _⟩))).differentiableAt (by simp)
  exact outer.comp time (differentiableAt_const point |>.prodMk differentiableAt_id)

/-- The first integrated force identity, in its nonsingular Cartesian
numerator form, follows from the first two literal cell equations. -/
theorem literal_first_force_numerator (mapping : Plane → ℝ → Vec) (potential : Plane → ℝ → ℝ)
    (radius : ℝ) (radiusLarge : 1 < radius)
    (mappingSmooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (potentialSmooth : ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ))
    (firstZero : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time, firstCellRow mapping potential point time = 0)
    (secondZero : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time, secondCellRow mapping potential point time = 0)
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    inner ℝ (diskEuler mapping point time) (diskAngular (diskAngular mapping) point time) -
      inner ℝ (diskAngular mapping point time) (diskEuler (diskAngular mapping) point time) +
      2 * ‖point‖ ^ 2 = 0 := by
  have pointIn : point ∈ Metric.ball (0 : Plane) radius := by
    simpa using pointBound.trans_lt radiusLarge
  have angularSmooth := diskAngular_joint_smooth mappingSmooth
  have eulerSmooth := diskEuler_joint_smooth mappingSmooth
  have potentialEulerSmooth := diskEuler_joint_smooth potentialSmooth
  have potentialAngularSmooth := diskAngular_joint_smooth potentialSmooth
  have angularDiff := smooth_spatial_differentiable angularSmooth point pointIn time
  have eulerDiff := smooth_spatial_differentiable eulerSmooth point pointIn time
  have potentialEulerDiff := smooth_spatial_differentiable potentialEulerSmooth point pointIn time
  have potentialAngularDiff := smooth_spatial_differentiable potentialAngularSmooth point pointIn time
  let row := fun argument cell => diskEuler potential argument cell -
    inner ℝ (diskEuler mapping argument cell) (diskAngular mapping argument cell)
  have rowSmooth : ContDiffOn ℝ ∞ (Function.uncurry row) (Metric.ball 0 radius ×ˢ univ) :=
    potentialEulerSmooth.sub (eulerSmooth.inner ℝ angularSmooth)
  have rowAngular : diskAngular row point time = 0 :=
    projected_zero_diskAngular row time (fun argument bound => secondZero argument bound time)
      point pointBound (smooth_spatial_differentiable rowSmooth point pointIn time)
  change diskAngular (fun argument cell => diskEuler potential argument cell -
    inner ℝ (diskEuler mapping argument cell) (diskAngular mapping argument cell)) point time = 0 at rowAngular
  rw [diskAngular_sub _ _ point time potentialEulerDiff (eulerDiff.inner ℝ angularDiff),
    diskAngular_inner _ _ point time eulerDiff angularDiff,
    diskAngular_diskEuler potentialSmooth point pointIn time,
    diskAngular_diskEuler mappingSmooth point pointIn time] at rowAngular
  have radiusDiff : DifferentiableAt ℝ (fun argument : Plane => ‖argument‖ ^ 2) point :=
    differentiableAt_id.norm_sq ℝ
  have firstDerivative :
      fderiv ℝ (fun argument => diskAngular potential argument time) point =
      fderiv ℝ (fun argument => ‖diskAngular mapping argument time‖ ^ 2 - ‖argument‖ ^ 2) point := by
    apply spatial_fderiv_eq_on_closedDisk _ _ _ point pointBound potentialAngularDiff
      ((angularDiff.norm_sq ℝ).sub radiusDiff)
    intro argument argumentIn
    have identity := firstZero argument (by simpa using argumentIn) time
    unfold firstCellRow at identity
    change diskAngular potential argument time = ‖diskAngular mapping argument time‖ ^ 2 - ‖argument‖ ^ 2
    linarith
  have potentialEuler : diskEuler (diskAngular potential) point time =
      2 * inner ℝ (diskAngular mapping point time) (diskEuler (diskAngular mapping) point time) -
        2 * ‖point‖ ^ 2 := by
    have derivative := congrArg (fun linear : Plane →L[ℝ] ℝ => linear point) firstDerivative
    change diskEuler (diskAngular potential) point time =
      diskEuler (fun argument cell => ‖diskAngular mapping argument cell‖ ^ 2 - ‖argument‖ ^ 2) point time at derivative
    rw [derivative, diskEuler_sub _ _ point time (angularDiff.norm_sq ℝ) radiusDiff,
      diskEuler_norm_sq _ point time angularDiff, diskEuler_radius_sq]
  rw [potentialEuler] at rowAngular
  have symmetry := real_inner_comm (diskEuler (diskAngular mapping) point time)
    (diskAngular mapping point time)
  linarith

end Grad.PhysicalEquilibrium
