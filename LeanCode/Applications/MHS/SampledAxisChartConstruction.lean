import SampledAxisBasics
import SampledAxisChartData
import SampledThresholdFamily

noncomputable section

open Set Filter
open scoped ContDiff

namespace Grad.MainAssembly.SampledAxisChartConstruction

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledThresholdFamily
open Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.SampledAxisBasics
open Grad.MainAssembly.SampledAxisChartData

private theorem planarPart_norm_sq (point : Vec) :
    ‖planarPart point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [planarPart, Fin.sum_univ_two]

private theorem axisPoint_mem (radius time : ℝ) :
    radius • axisRadial time ∈ roundAxis radius := by
  refine ⟨time, ?_⟩
  ext coordinate
  fin_cases coordinate <;> simp [axisRadial, vector]

/-- The ambient physical conclusions for the canonical sampled representative
provide the exact axis chart required by the normal-Hessian consumer. -/
theorem sampledRepresentative_hasSampledAxisChartSeedData
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (physical : PhysicalConclusions
      (sampledRepresentativeFamily cellLength family period epsilonIn 0
        parameter) cellLength period) :
    HasSampledAxisChartSeedData
      (sampledRepresentativeFamily cellLength family period epsilonIn 0
        parameter)
      ((period : ℝ) * cellLength) period family.rho family.alpha family.delta
      parameter.val := by
  dsimp [PhysicalConclusions] at physical
  rcases physical with
    ⟨_, magnetic, pressure, _, pressureSmoothNear, represents, _, _,
      axisInterior, criticalSet, _, _, _, _, _⟩
  let representative :=
    sampledRepresentativeFamily cellLength family period epsilonIn 0 parameter
  let chart : ℝ → Vec → Vec := fun _ =>
    sampledPositionCoordinateValue cellLength family period parameter.val
  let coordinatePoint : ℝ → Vec := fun time => vector 0 0 time
  let scale : ℝ → ℝ := fun time =>
    normalizedFactor
      (family.tilt (sampledEpsilon period) parameter.val
        ((period : ℝ) * time))
  let tilt : ℝ → Fin 2 → ℝ := fun time coordinate =>
    family.tilt (sampledEpsilon period) parameter.val
      ((period : ℝ) * time) coordinate
  refine ⟨pressure, chart, coordinatePoint, 0, scale, tilt, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro point
    exact (represents point).2
  · intro time
    exact normalizedFactor_positive cellLength family period epsilonIn parameter
      ((period : ℝ) * time)
  · intro time
    dsimp [chart, coordinatePoint]
    change sampledPositionJointLift cellLength family period
        (parameter.val, vector 0 0 time) = _
    rw [sampledPositionJointLift_eq]
    have planarZero : planarPart (vector 0 0 time) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [planarPart, vector]
    rw [planarZero]
    have timeCoordinate : (vector 0 0 time : Vec) 2 = time := by
      simp [vector]
    rw [timeCoordinate]
    exact sampledPosition_axis cellLength family period epsilonIn parameter time
  · intro time
    rcases pressureSmoothNear with
      ⟨neighborhood, neighborhoodOpen, bodySubset, pressureSmooth⟩
    have axisMem :
        ((period : ℝ) * cellLength) • axisRadial time ∈
          roundAxis ((period : ℝ) * cellLength) :=
      axisPoint_mem ((period : ℝ) * cellLength) time
    have bodyMem :
        ((period : ℝ) * cellLength) • axisRadial time ∈
          Set.range representative.position :=
      interior_subset (axisInterior axisMem)
    have neighborhoodMem := bodySubset bodyMem
    have smoothAt : ContDiffAt ℝ ∞ pressure
        (((period : ℝ) * cellLength) • axisRadial time) :=
      pressureSmooth.contDiffAt
        (neighborhoodOpen.mem_nhds neighborhoodMem)
    have chartAt : chart time (coordinatePoint time) =
        ((period : ℝ) * cellLength) • axisRadial time := by
      dsimp [chart, coordinatePoint]
      change sampledPositionJointLift cellLength family period
          (parameter.val, vector 0 0 time) = _
      rw [sampledPositionJointLift_eq]
      have planarZero : planarPart (vector 0 0 time) = 0 := by
        ext coordinate
        fin_cases coordinate <;> simp [planarPart, vector]
      rw [planarZero]
      simpa [vector] using
        sampledPosition_axis cellLength family period epsilonIn parameter time
    rw [chartAt]
    exact smoothAt.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  · intro time
    dsimp [chart, coordinatePoint]
    exact sampledPositionCoordinateValue_contDiffAt_axis cellLength family
      period epsilonIn parameter time
  · intro time
    have axisMem :
        ((period : ℝ) * cellLength) • axisRadial time ∈
          roundAxis ((period : ℝ) * cellLength) :=
      axisPoint_mem ((period : ℝ) * cellLength) time
    have criticalMem :
        ((period : ℝ) * cellLength) • axisRadial time ∈
          {point | point ∈ Set.range representative.position ∧
            fderiv ℝ pressure point = 0} := by
      rw [criticalSet]
      exact axisMem
    have chartAt : chart time (coordinatePoint time) =
        ((period : ℝ) * cellLength) • axisRadial time := by
      dsimp [chart, coordinatePoint]
      change sampledPositionJointLift cellLength family period
          (parameter.val, vector 0 0 time) = _
      rw [sampledPositionJointLift_eq]
      have planarZero : planarPart (vector 0 0 time) = 0 := by
        ext coordinate
        fin_cases coordinate <;> simp [planarPart, vector]
      rw [planarZero]
      simpa [vector] using
        sampledPosition_axis cellLength family period epsilonIn parameter time
    rw [chartAt]
    exact criticalMem.2
  · intro time
    let collar : Set Vec := planarPart ⁻¹' Metric.ball 0 1
    have collarOpen : IsOpen collar :=
      Metric.isOpen_ball.preimage planarPart_contDiff.continuous
    have coordinateIn : coordinatePoint time ∈ collar := by
      change planarPart (vector 0 0 time) ∈ Metric.ball 0 1
      have planarZero : planarPart (vector 0 0 time) = 0 := by
        ext coordinate
        fin_cases coordinate <;> simp [planarPart, vector]
      rw [Metric.mem_ball, dist_zero_right, planarZero, norm_zero]
      norm_num
    have collarNeighborhood : collar ∈ nhds (coordinatePoint time) :=
      collarOpen.mem_nhds coordinateIn
    filter_upwards [collarNeighborhood] with point pointIn
    have pointInCylinder : point ∈ cylinder := by
      change ‖planarPart point‖ ≤ 1
      exact le_of_lt (by
        simpa [collar, Metric.mem_ball, dist_zero_right] using pointIn)
    have parameterIn := parameter_mem_open cellLength family parameter
    have positionLift :=
      periodicLift_sampledRepresentativeExtension_position cellLength family
        period epsilonIn 0 parameter.val parameterIn point pointInCylinder
    have pressureLift :=
      periodicLift_sampledRepresentativeExtension_pressure cellLength family
        period epsilonIn 0 parameter.val parameterIn point pointInCylinder
    calc
      (pressure ∘ chart time) point =
          pressure (periodicLift representative.position point) := by
            change pressure
                (sampledPositionCoordinateValue cellLength family period
                  parameter.val point) =
              pressure (periodicLift
                (sampledRepresentativeExtension cellLength family period
                  epsilonIn 0 parameter.val).position point)
            apply congrArg pressure
            change sampledPositionJointLift cellLength family period
                (parameter.val, point) = _
            rw [sampledPositionJointLift_eq]
            exact positionLift.symm
      _ = pressure
          (representative.position (quotientPoint point pointInCylinder)) := by
            simp [periodicLift, pointInCylinder]
      _ = representative.pressure
          (quotientPoint point pointInCylinder) :=
            (represents (quotientPoint point pointInCylinder)).2
      _ = periodicLift representative.pressure point := by
            simp [periodicLift, pointInCylinder]
      _ = sampledPressureLift 0 (planarPart point) (point 2) := by
            simpa [representative, sampledRepresentativeFamily] using pressureLift
      _ = coordinatePressure 0 point := by
            change 0 - ‖planarPart point‖ ^ 2 =
              0 - point 0 ^ 2 - point 1 ^ 2
            rw [planarPart_norm_sq]
            ring
  · intro time
    dsimp [chart, coordinatePoint, scale, tilt]
    exact sampledPosition_hasAxisDerivative cellLength family period epsilonIn
      parameter time

/-- Threshold-specialized wrapper for the exact period-indexed family used by
the main theorem integration. -/
theorem exactSampledTargetFamily_hasSampledAxisChartSeedData
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (periodAfter : firstSampledPeriod cellLength family ≤ period)
    (parameter : Set.Icc family.lower family.upper)
    (physical : PhysicalConclusions
      (exactSampledTargetFamily cellLength family period parameter)
      cellLength period) :
    HasSampledAxisChartSeedData
      (exactSampledTargetFamily cellLength family period parameter)
      ((period : ℝ) * cellLength) period family.rho family.alpha family.delta
      parameter.val := by
  rw [exactSampledTargetFamily_eq cellLength family period periodAfter] at physical
  rw [exactSampledTargetFamily_eq cellLength family period periodAfter]
  exact sampledRepresentative_hasSampledAxisChartSeedData cellLength family
    period
    (sampledEpsilon_mem_after_firstPeriod cellLength family period periodAfter)
    parameter physical

end Grad.MainAssembly.SampledAxisChartConstruction
