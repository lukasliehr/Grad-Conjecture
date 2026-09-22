import AKDQ24AxisContinuityExtension

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

theorem actual_force_zero_closedCylinder (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (injective : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    let position := sampledPositionCoordinateValue length family period parameter.val
    let argument := coordinateDirection point time
    cross (magnetic (position argument)) (curl magnetic (position argument)) + gradient pressure (position argument) = 0 := by
  let field : Plane → Vec := fun point =>
    let position := sampledPositionCoordinateValue length family period parameter.val
    let argument := coordinateDirection point time
    cross (magnetic (position argument)) (curl magnetic (position argument)) + gradient pressure (position argument)
  have punctured (current : Plane) (currentBound : ‖current‖ ≤ 1) (nonzero : current ≠ 0) : field current = 0 := by
    have pairings := actual_force_coordinate_pairings_zero length family period periodPositive epsilonIn potential parameter
      magnetic pressure magneticSmooth pressureSmooth same current currentBound time
    exact vector_zero_of_coordinate_pairings _ (injective current currentBound time) current nonzero _
      pairings.1 pairings.2.1 pairings.2.2
  by_cases nonzero : point ≠ 0
  · exact punctured point pointBound nonzero
  · have pointZero : point = 0 := not_ne_iff.mp nonzero
    subst point
    have insertionSmooth : ContDiff ℝ ∞ (fun point : Plane => coordinateDirection point time) := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;> simp [coordinateDirection, vector] <;> fun_prop
    have argumentIn : coordinateDirection (0 : Plane) time ∈ sampledAmbientCollar family :=
      sampledAmbientCollar_contains family (referenceCoverPoint_mem ((⟨0, by simp⟩ : ClosedDisk), time))
    have positionContinuous := (sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1.contDiffAt
      ((sampledAmbientCollar_isOpen family).mem_nhds argumentIn) |>.continuousAt
    have positionSectionContinuous : ContinuousAt (fun point : Plane =>
        sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time)) 0 :=
      positionContinuous.comp (f := fun point : Plane => coordinateDirection point time)
        insertionSmooth.continuous.continuousAt
    have fieldContinuous : ContinuousAt field 0 :=
      (ambient_force_smooth magnetic pressure magneticSmooth pressureSmooth).continuous.continuousAt.comp
        (f := fun point : Plane => sampledPositionCoordinateValue length family period parameter.val
          (coordinateDirection point time)) positionSectionContinuous
    exact zero_at_axis_of_punctured_zero field fieldContinuous punctured

end Grad.PhysicalEquilibrium
