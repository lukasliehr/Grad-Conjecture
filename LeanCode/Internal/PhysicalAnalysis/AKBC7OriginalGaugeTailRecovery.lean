import AKBC6OriginalCovariantChart

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (angular cell : ℕ)

def originalCovariantTail (field : NegativeTrace parameters angular cell 3) : NegativeTrace parameters angular cell 2 :=
  fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 2)
    (fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters) field)

theorem originalCovariantTail_constant (field : NegativeTrace parameters angular cell 3) :
    IsAngularConstant parameters angular cell (originalCovariantTail parameters angular cell field) :=
  angularMeanKernel_action_constant parameters angular cell _

theorem originalCovariantUngauged_tailMean (field : NegativeTrace parameters angular cell 3) :
    fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 2)
      (fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters)
        (originalCovariantUngauged parameters angular cell field)) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularMeanKernel,scalarModeDiagonalKernel_action_coefficient,gaugeTailProjectionKernel,
    constantMatrixKernel_action_coefficient,originalCovariantUngauged,originalTraceVector_coefficient,
    forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient]
  apply PiLp.ext
  intro component
  by_cases zero : mode.1=0
  all_goals
    fin_cases component <;>
      simp [gaugeTailProjectionMap,matrixUnit_apply,operatorBasis,negativeTraceCoefficient,
        angularMeanMultiplier,angularMeanFreeMultiplier,zero]

theorem originalCovariantUngauged_plus_tail (field : NegativeTrace parameters angular cell 3) :
    originalCovariantUngauged parameters angular cell field+
      fullNegativeKernelAction parameters angular cell (tailInjectionKernel parameters)
        (originalCovariantTail parameters angular cell field)=field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [negativeTraceCoefficient_add,originalCovariantUngauged,originalTraceVector_coefficient,
    originalCovariantTail,angularMeanKernel,scalarModeDiagonalKernel_action_coefficient,
    gaugeTailProjectionKernel,tailInjectionKernel,constantMatrixKernel_action_coefficient]
  apply PiLp.ext
  intro component
  by_cases zero : mode.1=0
  all_goals
    fin_cases component <;>
      simp [gaugeTailProjectionMap,tailInjectionMap,matrixUnit_apply,operatorBasis,forceMeanFreeTrace,
        angularMeanFreeKernel,forceCoordinateTrace,coordinateProjectionKernel_action_coefficient,
        scalarModeDiagonalKernel_action_coefficient,angularMeanMultiplier,angularMeanFreeMultiplier,zero]

/-- Both original physical gauge means recover exactly the same immutable
Gamma correction, for the actual original covariant decomposition. -/
theorem originalCovariantGauge_recovers (length compact : ℝ)
    (state : RadialCoefficientState parameters length compact) (radius : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7≤radialGaugeLowRadius parameters length compact)
    (field : NegativeTrace (radialKernelParameters parameters radius) angular cell 3)
    (gauged : radialPhysicalGaugeMeans parameters length compact state radius angular cell field=0) :
    fullNegativeKernelAction (radialKernelParameters parameters radius) angular cell
      (radialGaugeQKernel parameters length compact state radius small)
      (originalCovariantUngauged (radialKernelParameters parameters radius) angular cell field)=field := by
  have correction := (radialGauge_constraint_iff parameters length compact state radius small angular cell
    (originalCovariantUngauged (radialKernelParameters parameters radius) angular cell field)
    (originalCovariantTail (radialKernelParameters parameters radius) angular cell field)
    (originalCovariantTail_constant (radialKernelParameters parameters radius) angular cell field)
    (originalCovariantUngauged_tailMean (radialKernelParameters parameters radius) angular cell field)).mp
      ((congrArg (radialPhysicalGaugeMeans parameters length compact state radius angular cell)
        (originalCovariantUngauged_plus_tail (radialKernelParameters parameters radius) angular cell field)).trans gauged)
  rw [radialGaugeQKernel_action_eq,← correction,
    originalCovariantUngauged_plus_tail (radialKernelParameters parameters radius) angular cell field]

end Grad.OriginalKernelCovariantRecovery
