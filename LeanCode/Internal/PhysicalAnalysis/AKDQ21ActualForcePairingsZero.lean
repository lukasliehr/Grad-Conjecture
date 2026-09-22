import AKDQ20ActualTimeForcePairing

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

theorem actual_force_coordinate_pairings_zero (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
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
    let force := cross (magnetic (position argument)) (curl magnetic (position argument)) + gradient pressure (position argument)
    inner ℝ force (fderiv ℝ position argument (coordinateDirection point 0)) = 0 ∧
    inner ℝ force (fderiv ℝ position argument (coordinateDirection (planeQuarterTurn point) 0)) = 0 ∧
    inner ℝ force (fderiv ℝ position argument (coordinateDirection 0 1)) = 0 := by
  have rows := actual_cell_integrated_equations length family (sampledEpsilon period) epsilonIn parameter
    point pointBound ((period : ℝ) * time)
  have radial := actual_force_disk_pairing length family period epsilonIn potential parameter magnetic pressure
    magneticSmooth pressureSmooth same point pointBound time point
  have angular := actual_force_disk_pairing length family period epsilonIn potential parameter magnetic pressure
    magneticSmooth pressureSmooth same point pointBound time (planeQuarterTurn point)
  have temporal := actual_force_time_pairing length family period periodPositive epsilonIn potential parameter magnetic pressure
    magneticSmooth pressureSmooth same point pointBound time
  dsimp only at rows radial angular temporal ⊢
  let mapping := family.v (sampledEpsilon period) parameter.val
  let cellTime := (period : ℝ) * time
  have first : inner ℝ (diskEuler mapping point cellTime) (diskAngular (diskAngular mapping) point cellTime) -
      inner ℝ (diskAngular mapping point cellTime) (diskEuler (diskAngular mapping) point cellTime) +
        2 * ‖point‖ ^ 2 = 0 := rows.1
  change _ = inner ℝ (diskAngular mapping point cellTime) (diskEuler (diskAngular mapping) point cellTime) -
    inner ℝ (diskEuler mapping point cellTime) (diskAngular (diskAngular mapping) point cellTime) -
      2 * inner ℝ point point at radial
  rw [real_inner_self_eq_norm_sq] at radial
  change _ = inner ℝ (diskAngular mapping point cellTime) (diskAngular (diskAngular mapping) point cellTime) -
    inner ℝ (diskAngular mapping point cellTime) (diskAngular (diskAngular mapping) point cellTime) -
      2 * inner ℝ point (planeQuarterTurn point) at angular
  rw [sub_self, inner_planeQuarterTurn_self, mul_zero, sub_zero] at angular
  rw [rows.2.1, mul_zero] at temporal
  exact ⟨by linarith only [first, radial], angular, temporal⟩

end Grad.PhysicalEquilibrium
