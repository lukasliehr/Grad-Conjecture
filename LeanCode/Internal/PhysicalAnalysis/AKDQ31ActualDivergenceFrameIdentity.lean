import AKDQ30ActualCellJacobianRate

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

theorem sampling_tangent_rescaling (period : ℕ) (positive : 0 < period) (first second : Vec) :
    first + (period : ℝ) • second =
      (period : ℝ) • (second + sampledEpsilon period • first) := by
  have product : (period : ℝ) * sampledEpsilon period = 1 := by
    unfold sampledEpsilon
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr positive.ne')
  rw [smul_add, smul_smul, product, one_smul, add_comm]

theorem actual_divergence_times_frame_zero (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    let position := sampledPositionCoordinateValue length family period parameter.val
    let argument := coordinateDirection point time
    divergence magnetic (position argument) *
      tripleDeterminant (fderiv ℝ position argument (coordinateDirection point 0))
        (fderiv ℝ position argument (coordinateDirection (planeQuarterTurn point) 0))
        (fderiv ℝ position argument (coordinateDirection 0 1)) = 0 := by
  have mappingSmooth := fixed_cell_joint_smooth family.vSmooth (sampledEpsilon period) epsilonIn parameter.val
    (parameter_mem_open length family parameter)
  have angularSmooth := diskAngular_joint_smooth mappingSmooth
  have pointIn : point ∈ Metric.ball (0 : Plane) family.collarRadius := by
    simpa using pointBound.trans_lt family.collarLarge
  have derivatives := actual_reconstructed_derivatives length family period epsilonIn potential parameter
    magnetic pressure magneticSmooth pressureSmooth same point pointBound time
  have chain (direction : Vec) :
      fderiv ℝ magnetic (sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time))
        (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val) (coordinateDirection point time) direction) =
      fderiv ℝ (actualMagneticLift length family period parameter.val) (coordinateDirection point time) direction :=
    congrArg (fun linear : Vec →L[ℝ] Vec => linear direction) derivatives.2.1
  have fieldEuler := rotatedSampledField_fderiv_disk period angularSmooth point pointIn time point
  have fieldAngular := rotatedSampledField_fderiv_disk period angularSmooth point pointIn time (planeQuarterTurn point)
  have fieldTime := rotatedSampledField_fderiv_time period angularSmooth point pointIn time
  change fderiv ℝ (actualMagneticLift length family period parameter.val) _ _ = _ at fieldEuler fieldAngular fieldTime
  dsimp only
  unfold divergence
  rw [← tripleDeterminant_linear_trace, chain, chain, chain, fieldEuler, fieldAngular, fieldTime,
    sampledPositionCoordinateValue_fderiv_disk_allPoints length family period epsilonIn parameter point pointBound time point,
    sampledPositionCoordinateValue_fderiv_disk_allPoints length family period epsilonIn parameter point pointBound time (planeQuarterTurn point),
    sampledPositionCoordinateValue_fderiv_toroidal_allPoints length family period periodPositive epsilonIn parameter point pointBound time 1]
  simp only [tripleDeterminant_rotation, mul_one]
  rw [sampling_tangent_rescaling period periodPositive]
  simp only [tripleDeterminant_smul_third]
  have rate := actual_cell_jacobian_rate_zero length family (sampledEpsilon period) epsilonIn parameter point pointBound ((period : ℝ) * time)
  rw [← mul_add, ← mul_add]
  change (period : ℝ) * (tripleDeterminant _ _ _ + tripleDeterminant _ _ _ + tripleDeterminant _ _ _) = 0
  simpa only [diskEuler, diskAngular, mul_zero] using congrArg (fun scalar : ℝ => (period : ℝ) * scalar) rate

end Grad.PhysicalEquilibrium
