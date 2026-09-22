import AHS6RadialEncodedSupport

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

abbrev forceCoordinateTrace (parameters : PhaseParameters) (angular cell : ℕ) (coordinate : Fin 3) :=
  fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 coordinate)

abbrev forceMeanTrace (parameters : PhaseParameters) (angular cell : ℕ) :=
  fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 1)

abbrev forceMeanFreeTrace (parameters : PhaseParameters) (angular cell : ℕ) :=
  fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1)

/-- All three decoded coordinates in the exact ambient J extension. -/
theorem encodedJ_first (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) :
    forceCoordinateTrace parameters angular cell 0
      (fullNegativeKernelAction parameters angular cell (encodedJKernel parameters) input) =
    forceMeanTrace parameters angular cell (forceCoordinateTrace parameters angular cell 0 input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  simp [forceCoordinateTrace, forceMeanTrace, coordinateProjectionKernel_action_coefficient,
    encodedJKernel, fullNegativeKernelAction_add, negativeTraceCoefficient_add,
    angularMeanComponentKernel, angularDoubleInverseComponentKernel, angularInverseComponentKernel,
    componentModeKernel_action_coefficient, angularMeanKernel, scalarModeDiagonalKernel_action_coefficient]

theorem encodedRotation_second (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) :
    forceCoordinateTrace parameters angular cell 1
      (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) input) =
    fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1)
      (forceCoordinateTrace parameters angular cell 1 input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  simp [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient,
    encodedRotationKernel, fullNegativeKernelAction_add, negativeTraceCoefficient_add,
    angularInverseComponentKernel, angularMeanFreeComponentKernel,
    componentModeKernel_action_coefficient, angularInverseKernel, scalarModeDiagonalKernel_action_coefficient]

theorem encodedRotation_third (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) :
    forceCoordinateTrace parameters angular cell 2
      (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) input) =
    forceMeanFreeTrace parameters angular cell (forceCoordinateTrace parameters angular cell 2 input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  simp [forceCoordinateTrace, forceMeanFreeTrace, coordinateProjectionKernel_action_coefficient,
    encodedRotationKernel, fullNegativeKernelAction_add, negativeTraceCoefficient_add,
    angularInverseComponentKernel, angularMeanFreeComponentKernel,
    componentModeKernel_action_coefficient, angularMeanFreeKernel, scalarModeDiagonalKernel_action_coefficient]

theorem forceCoordinate_meanFree (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) (coordinate : Fin 3)
    (supported : IsAngularMeanFreeComponent parameters angular cell coordinate input) :
    IsAngularMeanFree parameters angular cell (forceCoordinateTrace parameters angular cell coordinate input) := by
  intro axial
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  exact (coordinateProjectionKernel_action_coefficient parameters angular cell coordinate input (0, axial)).trans
    (supported axial)

theorem forceCoordinate_constant (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) (coordinate : Fin 3)
    (supported : IsAngularConstantComponent parameters angular cell coordinate input) :
    IsAngularConstant parameters angular cell (forceCoordinateTrace parameters angular cell coordinate input) := by
  intro mode nonzero
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  exact (coordinateProjectionKernel_action_coefficient parameters angular cell coordinate input mode).trans
    (supported mode nonzero)

theorem forceMean_meanFree_zero (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    forceMeanTrace parameters angular cell input = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [forceMeanTrace, angularMeanKernel, scalarModeDiagonalKernel_action_coefficient]
  by_cases zero : mode.1 = 0
  · have modeEq : mode = (0, mode.2) := Prod.ext zero rfl
    rw [modeEq, supported]
    simp [negativeTraceCoefficient]
  · simp [angularMeanMultiplier, zero, negativeTraceCoefficient]

theorem encodedRotation_second_derivative (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3)
    (supported : EncodedSupport parameters angular cell input) :
    IsAngularDerivative parameters angular cell
      (forceCoordinateTrace parameters angular cell 1
        (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) input))
      (forceCoordinateTrace parameters angular cell 1 input) := by
  rw [encodedRotation_second]
  exact angularInverseKernel_derivative parameters angular cell _
    (forceCoordinate_meanFree parameters angular cell input 1 supported.2.1)

end Grad.AnnularReconstruction
