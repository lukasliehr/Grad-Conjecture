import AKDQ17ActualAmbientDerivativeFidelity

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.MainAssembly.PhysicalNormalHessian Grad.PhysicalFamily.SampledGlobalEmbedding

theorem sampledPressure_global_smooth (potential : ℝ) : ContDiff ℝ ∞ (sampledPressureCoordinateValue potential) :=
  contDiff_const.sub ((contDiff_norm_sq ℝ).comp planarPart_contDiff)

theorem sampledPressure_fderiv_disk (potential : ℝ) (point direction : Plane) (time : ℝ) :
    fderiv ℝ (sampledPressureCoordinateValue potential) (coordinateDirection point time)
      (coordinateDirection direction 0) = -2 * inner ℝ point direction := by
  have smooth := (sampledPressure_global_smooth potential).differentiable (by simp)
  rw [← physical_disk_section_fderiv _ point time smooth.differentiableAt direction]
  have identity : (fun argument : Plane => sampledPressureCoordinateValue potential (coordinateDirection argument time)) =
      fun argument : Plane => potential - ‖argument‖ ^ 2 := by
    funext argument
    simp [sampledPressureCoordinateValue, sampledPressureLift]
  rw [identity]
  have derivative : fderiv ℝ (fun argument : Plane => potential - ‖argument‖ ^ 2) point =
      0 - fderiv ℝ (fun argument : Plane => ‖argument‖ ^ 2) point :=
    ((hasFDerivAt_const potential point).sub (differentiableAt_id.norm_sq ℝ).hasFDerivAt).fderiv
  rw [derivative]
  simp [fderiv_norm_sq_apply]

theorem sampledPressure_fderiv_time (potential : ℝ) (point : Plane) (time : ℝ) :
    fderiv ℝ (sampledPressureCoordinateValue potential) (coordinateDirection point time)
      (coordinateDirection 0 1) = 0 := by
  have smooth := (sampledPressure_global_smooth potential).differentiable (by simp)
  rw [← physical_time_section_fderiv _ point time smooth.differentiableAt]
  have identity : (fun current => sampledPressureCoordinateValue potential (coordinateDirection point current)) =
      fun _ : ℝ => potential - ‖point‖ ^ 2 := by
    funext current
    simp [sampledPressureCoordinateValue, sampledPressureLift]
  rw [identity]
  exact congrArg (fun linear : ℝ →L[ℝ] ℝ => linear 1) (hasFDerivAt_const (potential - ‖point‖ ^ 2) time).fderiv

theorem inner_planeQuarterTurn_self (point : Plane) : inner ℝ point (planeQuarterTurn point) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, planeQuarterTurn]
  ring

end Grad.PhysicalEquilibrium
