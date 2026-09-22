import AHS12ActualForceInverseConsumer

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

private abbrev rp (parameters : PhaseParameters) (r : RadialPoint) := radialKernelParameters parameters r

/-- The original normalized free chart q_*=(K A,xi/r,0). -/
def radialSevenFreeChart (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) : NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell (actualUnknownQAKernel (rp parameters r)) mass +
  fullNegativeKernelAction (rp parameters r) angular cell (secondCoordinateInjectionKernel (rp parameters r)) (input 3)

def radialSevenFreeChartRotation (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) : NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell (firstCoordinateInjectionKernel (rp parameters r)) mass +
  fullNegativeKernelAction (rp parameters r) angular cell (secondCoordinateInjectionKernel (rp parameters r)) (input 1)

theorem radialSevenFreeChart_derivative (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (rp parameters r) angular cell
      (radialSevenFreeChart parameters r angular cell mass input)
      (radialSevenFreeChartRotation parameters r angular cell mass input) :=
  (actualUnknownQAKernel_derivative (rp parameters r) angular cell mass massMean).add
    (scalarLaw.constantMatrix (matrixUnit 1 0))

theorem radialSevenFreeChart_first_meanFree (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    IsAngularMeanFreeComponent (rp parameters r) angular cell 0
      (radialSevenFreeChart parameters r angular cell mass input) := by
  intro axial
  simp only [radialSevenFreeChart, actualUnknownQAKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, negativeTraceCoefficient_add, PiLp.add_apply,
    firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, coordinateInjectionKernel_action_coefficient]
  simp [angularInverseKernel, scalarModeDiagonalKernel_action_coefficient, angularInverseMultiplier]

theorem radialSevenFreeChartRotation_first (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    forceCoordinateTrace (rp parameters r) angular cell 0
      (radialSevenFreeChartRotation parameters r angular cell mass input) = mass := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  simp [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient, radialSevenFreeChartRotation,
    negativeTraceCoefficient_add, firstCoordinateInjectionKernel, secondCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

def radialSevenEncodedTrace (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) : NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialUnknownWKernel parameters L compact state r small) mass +
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialKnownWKernel parameters L compact state r small)
    (sevenSlotFlatten (rp parameters r) angular cell input)

/-- The AE chart of the exact AHP encoded coordinates is precisely the
already constructed U A+a_* reconstruction. No inverse is selected again. -/
theorem radialSevenEncodedTrace_same_covariant (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    radialForceChart parameters L compact state r (small.trans (min_le_left _ _)) angular cell
      (radialSevenEncodedTrace parameters L compact state r small angular cell mass input)
      (radialSevenFreeChart parameters r angular cell mass input) =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialUnknownUKernel parameters L compact state r small) mass +
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialKnownAStarKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input) := by
  simp only [radialForceChart, radialSevenEncodedTrace, radialSevenFreeChart,
    radialUnknownUKernel, radialKnownAStarKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, fullNegativeKernelAction_add, sevenInputSlotKernel_action, map_add]
  abel

theorem radialSevenEncodedTrace_same_rotation (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    radialForceChartRotation parameters r angular cell
      (radialSevenEncodedTrace parameters L compact state r small angular cell mass input)
      (radialSevenFreeChartRotation parameters r angular cell mass input) =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialUnknownVKernel parameters L compact state r small) mass +
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialKnownRAStarKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input) := by
  simp only [radialForceChartRotation, radialSevenEncodedTrace, radialSevenFreeChartRotation,
    radialUnknownVKernel, radialKnownRAStarKernel, radialKnownRotatedQStarKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action, map_add]
  abel

end Grad.AnnularReconstruction
