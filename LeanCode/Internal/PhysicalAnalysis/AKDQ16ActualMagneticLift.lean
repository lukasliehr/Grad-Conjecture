import AKDQ15PullbackForcePairing

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding

def actualMagneticLift (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (parameter : ℝ) : Vec → Vec :=
  rotatedSampledField period (diskAngular (family.v (sampledEpsilon period) parameter))

@[simp] theorem actualMagneticLift_coordinateDirection (length : ℝ) (family : CellSolutionFamily length)
    (period : ℕ) (parameter : ℝ) (point : Plane) (time : ℝ) :
    actualMagneticLift length family period parameter (coordinateDirection point time) =
      rotation time (diskAngular (family.v (sampledEpsilon period) parameter) point ((period : ℝ) * time)) :=
  rotatedSampledField_coordinateDirection period _ point time

theorem actualMagneticLift_smooth (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) :
    ContDiffOn ℝ ∞ (actualMagneticLift length family period parameter.val) (sampledAmbientCollar family) :=
  rotatedSampledField_contDiffOn period (Grad.NonlinearQuotient.diskAngular_joint_smooth
    (fixed_cell_joint_smooth family.vSmooth (sampledEpsilon period) epsilonIn parameter.val
      (parameter_mem_open length family parameter)))

theorem actualMagneticLift_eq_stored (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ sampledAmbientCollar family) :
    actualMagneticLift length family period parameter.val point =
      sampledMagneticCoordinateValue length family period parameter.val point := by
  change _ = sampledMagneticJointLift length family period (parameter.val, point)
  rw [sampledMagneticJointLift_eq length family period epsilonIn (parameter.val, point)
    ⟨parameter_mem_open length family parameter, pointIn⟩]
  rfl

theorem actualMagneticLift_values (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper) (argument : ClosedDisk × ℝ) :
    actualMagneticLift length family period parameter.val (referenceCoverPoint argument) =
      (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic (referenceCover argument) := by
  rw [actualMagneticLift_eq_stored length family period epsilonIn parameter _
    (sampledAmbientCollar_contains family (referenceCoverPoint_mem argument))]
  exact (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).2.1

/-- The actual magnetic lift is the angular pushforward of the SAME sampled position. -/
theorem actualMagneticLift_pushforward (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val) (coordinateDirection point time)
      (coordinateDirection (planeQuarterTurn point) 0) =
        actualMagneticLift length family period parameter.val (coordinateDirection point time) := by
  rw [sampledPositionCoordinateValue_fderiv_disk_allPoints length family period epsilonIn parameter point pointIn time]
  change _ = rotatedSampledField period _ (coordinateDirection point time)
  rw [rotatedSampledField_coordinateDirection]
  rfl

end Grad.PhysicalEquilibrium
