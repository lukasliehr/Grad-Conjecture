import AKDQ16ActualMagneticLift

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

/-- Both literal chain rules for any smooth ambient representatives with the
accepted canonical values. Equality on the closed cylinder determines their
full derivatives at its axis and outer boundary. -/
theorem actual_reconstructed_derivatives (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
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
    let magneticLift := actualMagneticLift length family period parameter.val
    let argument := coordinateDirection point time
    magnetic (position argument) = magneticLift argument ∧
    (fderiv ℝ magnetic (position argument)).comp (fderiv ℝ position argument) = fderiv ℝ magneticLift argument ∧
    (fderiv ℝ pressure (position argument)).comp (fderiv ℝ position argument) =
      fderiv ℝ (sampledPressureCoordinateValue potential) argument := by
  let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
  let cover : ClosedDisk × ℝ := (⟨point, pointBound⟩, time)
  have argumentIn : coordinateDirection point time ∈ cylinder := referenceCoverPoint_mem cover
  have smooth := sampled_actual_lifts_smooth length family period epsilonIn potential parameter
  have positionSame := fun argument => (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).1
  have magneticSame := actualMagneticLift_values length family period epsilonIn potential parameter
  have pressureSame := fun argument => (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).2.2
  refine ⟨?_, ?_, ?_⟩
  · have positionValue := positionSame cover
    have magneticValue := magneticSame cover
    change magnetic (sampledPositionCoordinateValue length family period parameter.val (referenceCoverPoint cover)) =
      actualMagneticLift length family period parameter.val (referenceCoverPoint cover)
    rw [positionValue, magneticValue]
    exact (same (referenceCover cover)).1
  · exact reconstructedField_fderiv configuration.position configuration.magnetic
      (sampledPositionCoordinateValue length family period parameter.val)
      (actualMagneticLift length family period parameter.val) magnetic
      (sampledAmbientCollar family) (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family)
      smooth.1 (actualMagneticLift_smooth length family period epsilonIn parameter) magneticSmooth
      positionSame magneticSame (fun argument => (same argument).1) _ argumentIn
  · exact reconstructedField_fderiv configuration.position configuration.pressure
      (sampledPositionCoordinateValue length family period parameter.val)
      (sampledPressureCoordinateValue potential) pressure
      (sampledAmbientCollar family) (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family)
      smooth.1 smooth.2.2 pressureSmooth
      positionSame pressureSame (fun argument => (same argument).2) _ argumentIn

end Grad.PhysicalEquilibrium
