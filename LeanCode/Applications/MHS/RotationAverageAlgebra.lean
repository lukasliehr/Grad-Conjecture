import SmoothAngularAverage

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.MainTarget Grad.PhysicalFamily

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

theorem rotationAverage_const (value : Value) (point : Plane) :
    rotationAverage (fun _ => value) point = value := by
  rw [rotationAverage, intervalIntegral.integral_const]
  simp only [sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

theorem rotationAverage_origin (field : Plane → Value) :
    rotationAverage field 0 = field 0 := by
  simpa only [rotationAverage, physicalRotation_origin] using
    rotationAverage_const (field 0) (0 : Plane)

omit [CompleteSpace Value] in
theorem rotationAverage_rotation (field : Plane → Value) (angle : ℝ) (point : Plane) :
    rotationAverage field (planeRotationAction angle point) = rotationAverage field point := by
  unfold rotationAverage
  congr 1
  simp_rw [physicalRotation_add]
  rw [intervalIntegral.integral_comp_add_right (f := fun argument : ℝ =>
    field (planeRotationAction argument point))]
  simpa [zero_add, add_comm] using
    ((physicalRotation_periodic point).comp field).intervalIntegral_add_eq angle 0

omit [CompleteSpace Value] in
theorem rotationAverage_smul (scalar : ℝ) (field : Plane → Value) (point : Plane) :
    rotationAverage (fun argument => scalar • field argument) point =
      scalar • rotationAverage field point := by
  simp only [rotationAverage, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

omit [CompleteSpace Value] in
theorem rotationAverage_radial_pullout (field : Plane → Value) (point : Plane) :
    rotationAverage (fun argument => (‖argument‖ ^ 2 : ℝ) • field argument) point =
      (‖point‖ ^ 2 : ℝ) • rotationAverage field point := by
  simp only [rotationAverage, physicalRotation_norm, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

omit [CompleteSpace Value] [NormedSpace ℝ Value] in
theorem rotationSection_continuous {field : Plane → Value} {radius : ℝ}
    (continuous : ContinuousOn field (Metric.ball 0 radius))
    {point : Plane} (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    Continuous (fun angle => field (planeRotationAction angle point)) := by
  have rotationContinuous : Continuous (fun angle : ℝ => planeRotationAction angle point) := by
    unfold planeRotationAction
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;>
      simp [Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail] <;> fun_prop
  exact continuous.comp_continuous rotationContinuous
    (fun _ => by simpa [Metric.mem_ball, dist_zero_right] using pointIn)

omit [CompleteSpace Value] in
theorem rotationAverage_add {first second : Plane → Value} {radius : ℝ}
    (firstContinuous : ContinuousOn first (Metric.ball 0 radius))
    (secondContinuous : ContinuousOn second (Metric.ball 0 radius))
    {point : Plane} (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    rotationAverage (fun argument => first argument + second argument) point =
      rotationAverage first point + rotationAverage second point := by
  simp only [rotationAverage]
  rw [intervalIntegral.integral_add
    ((rotationSection_continuous firstContinuous pointIn).intervalIntegrable _ _)
    ((rotationSection_continuous secondContinuous pointIn).intervalIntegrable _ _), smul_add]

omit [CompleteSpace Value] in
theorem rotationAverage_sub {first second : Plane → Value} {radius : ℝ}
    (firstContinuous : ContinuousOn first (Metric.ball 0 radius))
    (secondContinuous : ContinuousOn second (Metric.ball 0 radius))
    {point : Plane} (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    rotationAverage (fun argument => first argument - second argument) point =
      rotationAverage first point - rotationAverage second point := by
  simp only [rotationAverage]
  rw [intervalIntegral.integral_sub
    ((rotationSection_continuous firstContinuous pointIn).intervalIntegrable _ _)
    ((rotationSection_continuous secondContinuous pointIn).intervalIntegrable _ _), smul_sub]

end Grad.Constraints
