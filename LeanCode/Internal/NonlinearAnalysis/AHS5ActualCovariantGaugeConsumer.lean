import AHS4RetainedFirstRowExtraction

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- J's second and third components have their exact zero means. -/
theorem gaugeTailMean_encodedJ (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) :
    fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 2)
      (fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters)
        (fullNegativeKernelAction parameters angular cell (encodedJKernel parameters) input)) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
    gaugeTailProjectionKernel, constantMatrixKernel_action_coefficient]
  have zeroCoefficient : negativeTraceCoefficient parameters angular cell (0 : NegativeTrace parameters angular cell 2) mode = 0 := by
    simp [negativeTraceCoefficient]
  rw [zeroCoefficient]
  by_cases zero : mode.1 = 0
  · simp only [angularMeanMultiplier, if_pos zero, one_smul]
    apply PiLp.ext
    intro component
    fin_cases component <;>
      simp [gaugeTailProjectionMap, matrixUnit_apply, operatorBasis, encodedJKernel,
        fullNegativeKernelAction_add, negativeTraceCoefficient_add,
        angularMeanComponentKernel, angularDoubleInverseComponentKernel,
        angularInverseComponentKernel, componentModeKernel_action_coefficient,
        angularDoubleInverseMultiplier, angularInverseMultiplier, zero]
  · simp [angularMeanMultiplier, zero]

theorem gaugeTailMean_first (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 1) :
    fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 2)
      (fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters)
        (fullNegativeKernelAction parameters angular cell (firstCoordinateInjectionKernel parameters) input)) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
    gaugeTailProjectionKernel, firstCoordinateInjectionKernel, coordinateInjectionKernel,
    constantMatrixKernel_action_coefficient]
  simp [gaugeTailProjectionMap, matrixUnit_apply, operatorBasis, negativeTraceCoefficient]

theorem gaugeTailMean_second (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 2)
      (fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters)
        (fullNegativeKernelAction parameters angular cell (secondCoordinateInjectionKernel parameters) input)) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
    gaugeTailProjectionKernel, secondCoordinateInjectionKernel, coordinateInjectionKernel,
    constantMatrixKernel_action_coefficient]
  have zeroCoefficient : negativeTraceCoefficient parameters angular cell (0 : NegativeTrace parameters angular cell 2) mode = 0 := by
    simp [negativeTraceCoefficient]
  rw [zeroCoefficient]
  by_cases zero : mode.1 = 0
  · have modeEq : mode = (0, mode.2) := Prod.ext zero rfl
    rw [modeEq, supported]
    simp
  · simp [angularMeanMultiplier, zero]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

theorem radialPhysicalGaugeMeans_add (angular cell : ℕ)
    (first second : NegativeTrace (rp parameters r) angular cell 3) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell (first + second) =
      radialPhysicalGaugeMeans parameters L compact state r angular cell first +
      radialPhysicalGaugeMeans parameters L compact state r angular cell second := by
  simp only [radialPhysicalGaugeMeans, map_add]
  abel

theorem radialUnknownUKernel_gauged
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 1) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialUnknownUKernel parameters L compact state r small) input) = 0 := by
  unfold radialUnknownUKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply radialGaugeQKernel_gauged
  simp only [fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, actualUnknownQAKernel, map_add]
  rw [gaugeTailMean_encodedJ, gaugeTailMean_first, add_zero]

theorem radialKnownAStarKernel_gauged
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (supported : IsAngularMeanFree (rp parameters r) angular cell (input 3)) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) = 0 := by
  unfold radialKnownAStarKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply radialGaugeQKernel_gauged
  simp only [fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, map_add, sevenInputSlotKernel_action]
  rw [gaugeTailMean_encodedJ, gaugeTailMean_second _ _ _ _ supported, add_zero]

/-- The actual original seven-slot covariant satisfies both original gauges
at every positive radius. Only the stated scalar zero-mean condition is needed. -/
theorem radialCovariantKernel_gauged
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialMassLowRadius parameters L compact) (positive : 0 < r.val)
    (angular cell : ℕ) (input : SevenSlotTrace (rp parameters r) angular cell)
    (supported : IsAngularMeanFree (rp parameters r) angular cell (input 3)) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialCovariantKernel parameters L compact state r small positive)
        (sevenSlotFlatten (rp parameters r) angular cell input)) = 0 := by
  unfold radialCovariantKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, radialSevenSlotKernel_action]
  unfold radialNormalizedCovariantKernel
  rw [fullNegativeKernelAction_add, radialPhysicalGaugeMeans_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    radialUnknownUKernel_gauged, zero_add]
  apply radialKnownAStarKernel_gauged
  intro axial
  change negativeTraceCoefficient (rp parameters r) angular cell ((r.val : ℂ)⁻¹ • input 3) (0, axial) = 0
  rw [negativeTraceCoefficient_smul, supported, smul_zero]

end Grad.AnnularReconstruction
