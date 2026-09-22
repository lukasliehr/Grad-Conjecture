import AHS8ActualForceChartCalculus

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

theorem encodedRotation_first_zero (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) :
    forceCoordinateTrace parameters angular cell 0
      (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) input) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  simp only [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient,
    encodedRotationKernel, fullNegativeKernelAction_add, negativeTraceCoefficient_add,
    PiLp.add_apply, angularInverseComponentKernel, angularMeanFreeComponentKernel,
    componentModeKernel_action_coefficient]
  simp [negativeTraceCoefficient]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

/-- The mean of AE12 retains the angularly constant x0 and removes no cell mode. -/
theorem radialFirstForceTrace_mean (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known) :
    forceMeanTrace (rp parameters r) angular cell
      (radialFirstForceTrace parameters L compact state r small angular cell encoded known) =
      -(2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 encoded +
      forceMeanTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell
          (radialForceKernel parameters L compact state r 0 0)
          (radialForceChart parameters L compact state r small angular cell encoded known)) := by
  have firstChart : forceCoordinateTrace (rp parameters r) angular cell 0
      (radialForceChart parameters L compact state r small angular cell encoded known) =
      forceCoordinateTrace (rp parameters r) angular cell 0 encoded +
        forceCoordinateTrace (rp parameters r) angular cell 0 known := by
    unfold radialForceChart
    rw [radialGaugeQ_first, map_add, encodedJ_first,
      angularMean_action_constant_eq _ _ _ _
        (forceCoordinate_constant (rp parameters r) angular cell encoded 0 supported.1)]
  have secondMean : forceMeanTrace (rp parameters r) angular cell
      (forceCoordinateTrace (rp parameters r) angular cell 1
        (fullNegativeKernelAction (rp parameters r) angular cell (encodedRotationKernel (rp parameters r)) encoded)) = 0 := by
    rw [encodedRotation_second]
    exact forceMean_meanFree_zero _ _ _ _ (angularInverseKernel_action_meanFree _ _ _ _)
  unfold radialFirstForceTrace
  rw [map_add, map_sub, map_neg, map_smul, secondMean, firstChart, map_add,
    forceMean_meanFree_zero _ _ _ _ (forceCoordinate_meanFree (rp parameters r) angular cell known 0 knownMean), add_zero,
    angularMean_action_constant_eq _ _ _ _
      (forceCoordinate_constant (rp parameters r) angular cell encoded 0 supported.1)]
  simp

/-- Split only by linearity of the same physical chart. -/
theorem radialForceChart_split (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3) :
    radialForceChart parameters L compact state r small angular cell encoded known =
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeDecodedKernel parameters L compact state r small) encoded +
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeQKernel parameters L compact state r small) known := by
  simp only [radialForceChart, radialGaugeDecodedKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, map_add]

def radialEncodedRowZero (angular cell : ℕ)
    (encoded : NegativeTrace (rp parameters r) angular cell 3) : NegativeTrace (rp parameters r) angular cell 1 :=
  -(2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 encoded +
  forceMeanTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeDecodedKernel parameters L compact state r small) encoded))

def radialEncodedRowOne (angular cell : ℕ)
    (encoded : NegativeTrace (rp parameters r) angular cell 3) : NegativeTrace (rp parameters r) angular cell 1 :=
  -forceCoordinateTrace (rp parameters r) angular cell 1 encoded +
  forceMeanFreeTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialRotatedForceKernel parameters L compact state r 0 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeDecodedKernel parameters L compact state r small) encoded) +
     fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (encodedRotationKernel (rp parameters r)) encoded))

def radialEncodedRowTwo (angular cell : ℕ)
    (encoded : NegativeTrace (rp parameters r) angular cell 3) : NegativeTrace (rp parameters r) angular cell 1 :=
  forceCoordinateTrace (rp parameters r) angular cell 2 encoded +
  forceMeanFreeTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeDecodedKernel parameters L compact state r small) encoded))

theorem radialEncodedSystem_scalar_rows
    (firstSmall : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (encoded : NegativeTrace (rp parameters r) angular cell 3) :
    let result := fullNegativeKernelAction (rp parameters r) angular cell
      (radialEncodedFirstSystemKernel parameters L compact state r firstSmall) encoded
    forceCoordinateTrace (rp parameters r) angular cell 0 result =
      radialEncodedRowZero parameters L compact state r (firstSmall.trans (min_le_left _ _)) angular cell encoded ∧
    forceCoordinateTrace (rp parameters r) angular cell 1 result =
      radialEncodedRowOne parameters L compact state r (firstSmall.trans (min_le_left _ _)) angular cell encoded ∧
    forceCoordinateTrace (rp parameters r) angular cell 2 result =
      radialEncodedRowTwo parameters L compact state r (firstSmall.trans (min_le_left _ _)) angular cell encoded := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
    intro mode
    apply PiLp.ext
    intro component
    have unique := Fin.eq_zero component
    subst component
    simp [forceCoordinateTrace, forceMeanTrace, forceMeanFreeTrace,
      radialEncodedRowZero, radialEncodedRowOne, radialEncodedRowTwo,
      coordinateProjectionKernel_action_coefficient, radialEncodedFirstSystemKernel,
      radialEncodedPerturbationKernel, radialEncodedE0Kernel, radialEncodedE1Kernel, radialEncodedE2Kernel,
      fullNegativeKernelAction_add, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
      negativeTraceCoefficient_add, firstCoordinateInjectionKernel, secondCoordinateInjectionKernel,
      thirdCoordinateInjectionKernel, coordinateInjectionKernel_action_coefficient,
      encodedD0Kernel, constantMatrixKernel_action_coefficient, diagonalThreeMap,
      matrixUnit_apply, operatorBasis, negativeTraceCoefficient_smul, negativeTraceCoefficient_neg]

end Grad.AnnularReconstruction
