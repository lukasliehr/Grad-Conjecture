import AKDQ8AffineAngularRule

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

/-- The third literal row and the angular derivative of the first row
supply the second force identity, including the axis and outer boundary. -/
theorem literal_second_force_numerator (length epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (potential : Plane → ℝ → ℝ)
    (radius : ℝ) (radiusLarge : 1 < radius)
    (mappingSmooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (potentialSmooth : ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ))
    (firstZero : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time, firstCellRow mapping potential point time = 0)
    (thirdZero : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time,
      thirdCellRow length epsilon mapping potential point time = 0)
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    inner ℝ (diskAngular mapping point time) (cellDerivative (diskAngular mapping) point time) -
      inner ℝ (affineStateDerivative length epsilon mapping point time)
        (diskAngular (diskAngular mapping) point time) = 0 := by
  have pointIn : point ∈ Metric.ball (0 : Plane) radius := by
    simpa using pointBound.trans_lt radiusLarge
  have angularSmooth := diskAngular_joint_smooth mappingSmooth
  have affineSmooth := affineStateDerivative_joint_smooth length epsilon mappingSmooth
  have potentialTimeSmooth := cellDerivative_joint_smooth potentialSmooth
  have angularDiff := smooth_spatial_differentiable angularSmooth point pointIn time
  have affineDiff := smooth_spatial_differentiable affineSmooth point pointIn time
  have potentialTimeDiff := smooth_spatial_differentiable potentialTimeSmooth point pointIn time
  have angularTimeDiff := smooth_time_differentiable angularSmooth point pointIn time
  let row := fun argument cell =>
    inner ℝ (diskAngular mapping argument cell) (affineStateDerivative length epsilon mapping argument cell) -
      cellDerivative potential argument cell
  have rowSmooth : ContDiffOn ℝ ∞ (Function.uncurry row) (Metric.ball 0 radius ×ˢ univ) :=
    (angularSmooth.inner ℝ affineSmooth).sub potentialTimeSmooth
  have rowAngular : diskAngular row point time = 0 :=
    projected_zero_diskAngular row time (fun argument bound => thirdZero argument bound time)
      point pointBound (smooth_spatial_differentiable rowSmooth point pointIn time)
  change diskAngular (fun argument cell =>
    inner ℝ (diskAngular mapping argument cell) (affineStateDerivative length epsilon mapping argument cell) -
      cellDerivative potential argument cell) point time = 0 at rowAngular
  rw [diskAngular_sub _ _ point time (angularDiff.inner ℝ affineDiff) potentialTimeDiff,
    diskAngular_inner _ _ point time angularDiff affineDiff,
    diskAngular_affineStateDerivative length epsilon mappingSmooth point pointIn time,
    diskAngular_cellDerivative potentialSmooth point pointIn time,
    inner_add_right, inner_smul_right, inner_tangentGenerator_self, mul_zero, add_zero] at rowAngular
  have firstIdentity : (fun cell => diskAngular potential point cell) =
      (fun cell => ‖diskAngular mapping point cell‖ ^ 2 - ‖point‖ ^ 2) := by
    funext cell
    have identity := firstZero point pointBound cell
    unfold firstCellRow at identity
    linarith
  have potentialTime : cellDerivative (diskAngular potential) point time =
      2 * inner ℝ (diskAngular mapping point time) (cellDerivative (diskAngular mapping) point time) := by
    have derivative := congrArg (fun field : ℝ → ℝ => fderiv ℝ field time 1) firstIdentity
    change cellDerivative (diskAngular potential) point time =
      cellDerivative (fun argument cell => ‖diskAngular mapping argument cell‖ ^ 2 - ‖argument‖ ^ 2) point time at derivative
    rw [derivative, cellDerivative_sub _ _ point time (angularTimeDiff.norm_sq ℝ) (differentiableAt_const _),
      cellDerivative_norm_sq _ point time angularTimeDiff]
    have constantDerivative : cellDerivative (fun argument (_ : ℝ) => ‖argument‖ ^ 2) point time = 0 :=
      congrArg (fun linear : ℝ →L[ℝ] ℝ => linear 1) (hasFDerivAt_const (‖point‖ ^ 2) time).fderiv
    rw [constantDerivative, sub_zero]
  rw [potentialTime] at rowAngular
  have symmetry := real_inner_comm (diskAngular (diskAngular mapping) point time)
    (affineStateDerivative length epsilon mapping point time)
  linarith

end Grad.PhysicalEquilibrium
