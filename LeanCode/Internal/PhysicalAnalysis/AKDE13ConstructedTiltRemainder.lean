import AKDE12RealChartFirstJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500
open Set Filter
open scoped ContDiff Topology

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.AxisSplit
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit Grad.Q24Realization
open Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

def constructedTilt (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) (cell : ℝ) :=
  originalRealTilt (smoothingChartCore parameters (scale.parameterLimit point).val).1 cell

def constructedCellRemainder (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (disk : SpatialPlane) (cell : ℝ) :=
  constructedCellVector scale point disk cell -
    (normalizedFactor (constructedTilt scale point cell) •
      planeEmbedding (seedAction (point.1 0) (point.1 1) (point.1 2) (point.1 3) cell disk) +
      planeDot (constructedTilt scale point cell) disk • tangentDirection)

def constructedChartState (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (seedInside : point.1 ∈ Seed.parameterDomain) : ChartState parameters :=
  ((smoothingChartCore parameters (scale.parameterLimit point).val).1,
    toPhysicalCore parameters (Gauges.seedTransfer parameters reference inside point.1 seedInside
      (scale.parameterLimit point).val.2.1), (scale.parameterLimit point).val.2.2)

theorem constructedChartState_zeroJets (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (seedInside : point.1 ∈ Seed.parameterDomain) :
    ∀ index, ZeroCartesianFirstJets ((constructedChartState scale point seedInside).2.1.val index) :=
  toPhysicalCore_zeroJets parameters _ (Gauges.seedTransfer_zero_first_jets parameters reference inside point.1 seedInside _
    (Grad.ConstrainedTransfer.smoothState_constraints parameters reference inside (scale.parameterLimit point)).1.1)

theorem constructedPhysicalChart_normalized (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    (constructedPhysicalChart scale point).2 = normalizedChart parameters point.1
      (scale.parameterLimit_admissible point member).1
      (constructedChartState scale point (scale.parameterLimit_admissible point member).1) := by
  rw [constructedPhysicalChart_same scale point member]
  rfl

theorem constructedTilt_bound (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (cell : ℝ) :
    ‖constructedTilt scale point cell‖ ^ 2 < 2 :=
  originalRealTilt_bound _ (stateChart_real parameters reference inside (scale.parameterLimit point)).1
    (scale.parameterLimit_admissible point member).2 cell

theorem constructedTilt_firstJet (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (direction : Fin 2) (cell : ℝ) :
    (fderiv ℝ (fun disk => constructedCellVector scale point disk cell) 0 (spatialBasis direction)) 1 =
      constructedTilt scale point cell direction := by
  unfold constructedCellVector
  rw [constructedPhysicalChart_normalized scale point member]
  exact normalizedRealChart_tilt_firstJet point.1 (scale.parameterLimit_admissible point member).1 _
    (constructedChartState_zeroJets scale point _) direction cell

theorem constructedCellRemainder_original (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (disk : ClosedDisk) (cell : ℝ) :
    constructedCellRemainder scale point disk.val cell =
      realCellVector (constructedChartState scale point (scale.parameterLimit_admissible point member).1).2.1 disk.val cell := by
  have formula := originalRealNormalizedChart_value point.1 (scale.parameterLimit_admissible point member).1
    (constructedChartState scale point (scale.parameterLimit_admissible point member).1)
    (stateChart_real parameters reference inside (scale.parameterLimit point)).1
    (scale.parameterLimit_admissible point member).2 disk cell
  change realCellVector (normalizedChart parameters point.1 (scale.parameterLimit_admissible point member).1
    (constructedChartState scale point (scale.parameterLimit_admissible point member).1)).1 disk.val cell = _ at formula
  unfold constructedCellRemainder constructedCellVector
  rw [constructedPhysicalChart_normalized scale point member,formula]
  change (_ + _ + _) - (_ + _) = _
  simp only [constructedChartState,constructedTilt]
  exact add_sub_cancel_left _ _

theorem constructedCellRemainder_zero_value (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (cell : ℝ) :
    constructedCellRemainder scale point 0 cell = 0 := by
  rw [show (0 : SpatialPlane) = originPoint.val from rfl,constructedCellRemainder_original scale point member originPoint cell]
  exact realCellVector_zeroJets_value _ (constructedChartState_zeroJets scale point _) cell

theorem constructedCellRemainder_zero_derivative (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (cell : ℝ) :
    fderiv ℝ (fun disk => constructedCellRemainder scale point disk cell) 0 = 0 := by
  have agree : (fun disk => constructedCellRemainder scale point disk cell) =ᶠ[𝓝 (0 : SpatialPlane)]
      (fun disk => realCellVector (constructedChartState scale point (scale.parameterLimit_admissible point member).1).2.1 disk cell) := by
    filter_upwards [Metric.ball_mem_nhds (0 : SpatialPlane) (by norm_num : (0:ℝ)<1)] with disk small
    exact constructedCellRemainder_original scale point member ⟨disk,(by simpa only [Metric.mem_ball,dist_zero_right] using small : ‖disk‖ < 1).le⟩ cell
  rw [agree.fderiv_eq]
  exact realCellVector_zeroJets_derivative _ (constructedChartState_zeroJets scale point _) cell

theorem constructedCell_normalized (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (disk : SpatialPlane) (cell : ℝ) :
    constructedCellVector scale point disk cell =
      normalizedFactor (constructedTilt scale point cell) •
        planeEmbedding (seedAction (point.1 0) (point.1 1) (point.1 2) (point.1 3) cell disk) +
      planeDot (constructedTilt scale point cell) disk • tangentDirection +
      constructedCellRemainder scale point disk cell := by
  unfold constructedCellRemainder
  abel

end Grad.OriginalCellFamily
