import AKDQ19ActualDiskForcePairing

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

theorem actual_force_time_pairing (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
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
    let mapping := family.v (sampledEpsilon period) parameter.val
    let cellTime := (period : ℝ) * time
    inner ℝ (cross (magnetic (position argument)) (curl magnetic (position argument)) + gradient pressure (position argument))
      (fderiv ℝ position argument (coordinateDirection 0 1)) =
        (period : ℝ) * (inner ℝ (diskAngular mapping point cellTime)
          (cellDerivative (diskAngular mapping) point cellTime) -
        inner ℝ (affineStateDerivative length (sampledEpsilon period) mapping point cellTime)
          (diskAngular (diskAngular mapping) point cellTime)) := by
  have mappingSmooth := fixed_cell_joint_smooth family.vSmooth (sampledEpsilon period) epsilonIn parameter.val
    (parameter_mem_open length family parameter)
  have angularSmooth := diskAngular_joint_smooth mappingSmooth
  have pointIn : point ∈ Metric.ball (0 : Plane) family.collarRadius := by
    simpa using pointBound.trans_lt family.collarLarge
  have derivatives := actual_reconstructed_derivatives length family period epsilonIn potential parameter
    magnetic pressure magneticSmooth pressureSmooth same point pointBound time
  have fieldTime := rotatedSampledField_fderiv_time period angularSmooth point pointIn time
  have fieldAngular := rotatedSampledField_fderiv_disk period angularSmooth point pointIn time (planeQuarterTurn point)
  have comparison := pullback_force_pairing
    (sampledPositionCoordinateValue length family period parameter.val)
    (actualMagneticLift length family period parameter.val) (sampledPressureCoordinateValue potential)
    magnetic pressure (coordinateDirection point time) (coordinateDirection (planeQuarterTurn point) 0)
    (coordinateDirection 0 1) derivatives.1
    (actualMagneticLift_pushforward length family period epsilonIn parameter point pointBound time)
    derivatives.2.1 derivatives.2.2
  change fderiv ℝ (actualMagneticLift length family period parameter.val) _ _ = _ at fieldTime fieldAngular
  rw [fieldTime, fieldAngular, actualMagneticLift_coordinateDirection,
    sampledPositionCoordinateValue_fderiv_toroidal_allPoints length family period periodPositive epsilonIn parameter point pointBound time,
    sampledPressure_fderiv_time, rotation_inner, rotation_inner] at comparison
  simp only [mul_one, inner_add_right, inner_smul_right, inner_smul_left,
    inner_tangentGenerator_self, zero_add, add_zero, conj_trivial] at comparison
  dsimp only
  rw [sampledPositionCoordinateValue_fderiv_toroidal_allPoints length family period periodPositive epsilonIn parameter point pointBound time]
  simpa only [mul_one, mul_sub, diskAngular] using comparison

end Grad.PhysicalEquilibrium
