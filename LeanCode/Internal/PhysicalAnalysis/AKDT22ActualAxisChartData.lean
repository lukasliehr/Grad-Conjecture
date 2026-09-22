import AKDT21ActualFoliatedFields
import SampledAxisChartData

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.SampledAxisChartData Grad.MainAssembly.CircleIsometryClassification
open Grad.PhysicalFamily.SampledGlobalEmbedding

/-- The actual normalized axis chart is constructed directly from the SAME
fields and their proved zero set, without assuming PhysicalConclusions. -/
theorem actual_axis_chart_data (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument) :
    HasSampledAxisChartSeedData (sampledRepresentativeFamily length family period epsilonIn potential parameter)
      ((period : ℝ) * length) period family.rho family.alpha family.delta parameter.val := by
  let chart : Vec → Vec := sampledPositionCoordinateValue length family period parameter.val
  have chartValue (time : ℝ) : chart (vector 0 0 time) = ((period : ℝ) * length) • axisRadial time := by
    have pointSame : vector 0 0 time = referenceCoverPoint (⟨0, by simp⟩, time) := by
      ext coordinate
      fin_cases coordinate <;> simp [referenceCoverPoint, coordinateDirection, vector]
    rw [pointSame]
    change sampledPositionCoordinateValue length family period parameter.val _ = _
    rw [(sampled_actual_lifts_values length family period epsilonIn potential parameter (⟨0, by simp⟩, time)).1]
    exact actual_position_axis length family period epsilonIn potential parameter time
  have criticalSet := (actual_field_zero_sets length family period epsilonIn potential parameter valid injective
    magnetic pressure magneticSmooth pressureSmooth same).1
  refine ⟨pressure, fun _ => chart, fun time => vector 0 0 time, potential,
    fun time => normalizedFactor (family.tilt (sampledEpsilon period) parameter.val ((period : ℝ) * time)),
    fun time coordinate => family.tilt (sampledEpsilon period) parameter.val ((period : ℝ) * time) coordinate,
    fun argument => (same argument).2, ?_, chartValue, ?_, ?_, ?_, ?_, ?_⟩
  · intro time
    exact normalizedFactor_positive length family period epsilonIn parameter ((period : ℝ) * time)
  · intro time
    exact pressureSmooth.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  · intro time
    exact sampledPositionCoordinateValue_contDiffAt_axis length family period epsilonIn parameter time
  · intro time
    change fderiv ℝ pressure (chart (vector 0 0 time)) = 0
    rw [chartValue]
    have axisIn : ((period : ℝ) * length) • axisRadial time ∈ roundAxis ((period : ℝ) * length) := by
      refine ⟨time, ?_⟩
      ext coordinate
      fin_cases coordinate <;> simp [axisRadial, vector]
    rw [← criticalSet] at axisIn
    exact axisIn.2
  · intro time
    have domainOpen : IsOpen {point : Vec | ‖planarPart point‖ < 1} :=
      isOpen_lt planarPart_contDiff.continuous.norm continuous_const
    have axisIn : vector 0 0 time ∈ {point : Vec | ‖planarPart point‖ < 1} := by
      have planarZero : planarPart (vector 0 0 time) = 0 := by ext coordinate; fin_cases coordinate <;> simp [planarPart, vector]
      change ‖planarPart (vector 0 0 time)‖ < 1
      rw [planarZero, norm_zero]
      norm_num
    filter_upwards [domainOpen.mem_nhds axisIn] with point pointIn
    let cover : ClosedDisk × ℝ := (⟨planarPart point, pointIn.le⟩, point 2)
    have pointSame : referenceCoverPoint cover = point := by
      ext coordinate
      fin_cases coordinate <;> simp [referenceCoverPoint, cover, coordinateDirection, planarPart, vector]
    have positionSame := (sampled_actual_lifts_values length family period epsilonIn potential parameter cover).1
    rw [pointSame] at positionSame
    change pressure (chart point) = coordinatePressure potential point
    rw [show chart point = (sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceCover cover) from positionSame,
      (same (referenceCover cover)).2,
      ← (sampled_actual_lifts_values length family period epsilonIn potential parameter cover).2.2, pointSame]
    change potential - ‖planarPart point‖ ^ 2 = potential - point 0 ^ 2 - point 1 ^ 2
    rw [Grad.NonlinearQuotient.disk_norm_sq]
    simp [planarPart]
    ring
  · intro time
    exact sampledPosition_hasAxisDerivative length family period epsilonIn parameter time

end Grad.PhysicalGeometry
