import AHS3ActualRetainedForceRow

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The original x,z,s coordinate decomposition, with no source slot removed. -/
theorem originalSevenTuple_decomposition (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 7) :
    input =
      fullNegativeKernelAction parameters angular cell (coordinateInjectionKernel parameters 7 0)
        (fullNegativeKernelAction parameters angular cell (sevenInputSlotKernel parameters 0) input) +
      fullNegativeKernelAction parameters angular cell (retainedTupleInsertionKernel parameters)
        (fullNegativeKernelAction parameters angular cell (retainedTupleProjectionKernel parameters) input) +
      fullNegativeKernelAction parameters angular cell (sourceTupleInsertionKernel parameters)
        (fullNegativeKernelAction parameters angular cell (sourceTupleProjectionKernel parameters) input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [negativeTraceCoefficient_add, coordinateInjectionKernel, sevenInputSlotKernel,
    coordinateProjectionKernel, retainedTupleInsertionKernel, retainedTupleProjectionKernel,
    sourceTupleInsertionKernel, sourceTupleProjectionKernel, constantMatrixKernel_action_coefficient]
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [retainedTupleInsertion_apply, retainedTupleProjection_apply,
      sourceTupleInsertion_apply, sourceTupleProjection_apply, matrixUnit_apply, operatorBasis]

theorem highAngular_action_meanFree_eq (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 1) :
    fullNegativeKernelAction parameters angular cell (highAngularKernel parameters 1)
      (fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1) input) =
    fullNegativeKernelAction parameters angular cell (highAngularKernel parameters 1) input := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [highAngularKernel, angularMeanFreeKernel, scalarModeDiagonalKernel_action_coefficient,
    smul_smul]
  by_cases zero : mode.1 = 0
  · simp [highAngularMultiplier, angularMeanFreeMultiplier, zero]
  · simp [angularMeanFreeMultiplier, zero]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact) (positive : 0 < r.val)
private abbrev rp := radialKernelParameters parameters r

/-- AI1/AI2: literal Q[(Ra_c)_1-r1 a_c] of the actual ordered reconstruction. -/
def radialRetainedFirstRowKernel : RadialKernel parameters r 7 1 :=
  fullKernelComposition (highAngularKernel (rp parameters r) 1)
    (fullKernelSub
      (fullKernelComposition (coordinateProjectionKernel (rp parameters r) 3 0)
        (radialRotatedCovariantKernel parameters L compact state r small positive))
      (fullKernelComposition (radialRetainedForceKernel parameters L compact state r)
        (radialCovariantKernel parameters L compact state r small positive)))

def radialRetainedAKernel : RadialKernel parameters r 1 1 :=
  fullKernelComposition (radialRetainedFirstRowKernel parameters L compact state r small positive)
    (coordinateInjectionKernel (rp parameters r) 7 0)

def radialRetainedJKernel : RadialKernel parameters r 3 1 :=
  fullKernelComposition (radialRetainedFirstRowKernel parameters L compact state r small positive)
    (retainedTupleInsertionKernel (rp parameters r))

def radialRetainedSKernel : RadialKernel parameters r 3 1 :=
  fullKernelComposition (radialRetainedFirstRowKernel parameters L compact state r small positive)
    (sourceTupleInsertionKernel (rp parameters r))

theorem radialRetainedFirstRowKernel_action (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 7) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialRetainedFirstRowKernel parameters L compact state r small positive) input =
    fullNegativeKernelAction (rp parameters r) angular cell (highAngularKernel (rp parameters r) 1)
      (fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 3 0)
        (fullNegativeKernelAction (rp parameters r) angular cell
          (radialRotatedCovariantKernel parameters L compact state r small positive) input) -
       fullNegativeKernelAction (rp parameters r) angular cell
        (radialRetainedForceKernel parameters L compact state r)
        (fullNegativeKernelAction (rp parameters r) angular cell
          (radialCovariantKernel parameters L compact state r small positive) input)) := by
  simp only [radialRetainedFirstRowKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, fullNegativeKernelAction_sub]

/-- The blocks are exactly the prescribed insertions, hence reproduce the
same full input-dependent kernel on every original seven-slot datum. -/
theorem radialRetainedFirstRow_extraction (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 7) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialRetainedFirstRowKernel parameters L compact state r small positive) input =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialRetainedAKernel parameters L compact state r small positive)
      (fullNegativeKernelAction (rp parameters r) angular cell (sevenInputSlotKernel (rp parameters r) 0) input) +
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialRetainedJKernel parameters L compact state r small positive)
      (fullNegativeKernelAction (rp parameters r) angular cell (retainedTupleProjectionKernel (rp parameters r)) input) +
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialRetainedSKernel parameters L compact state r small positive)
      (fullNegativeKernelAction (rp parameters r) angular cell (sourceTupleProjectionKernel (rp parameters r)) input) := by
  conv_lhs => rw [originalSevenTuple_decomposition (rp parameters r) angular cell input]
  simp only [map_add, radialRetainedAKernel, radialRetainedJKernel, radialRetainedSKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]

/-- The original P in AD9 is retained before Q, and eliminated only by the
proved QP=Q identity. This is exactly the signed first retained equation. -/
theorem radialRetainedFirstRow_equation_iff (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 7)
    (xiRadial source : NegativeTrace (rp parameters r) angular cell 1) :
    fullNegativeKernelAction (rp parameters r) angular cell (highAngularKernel (rp parameters r) 1)
      (fullNegativeKernelAction (rp parameters r) angular cell (angularMeanFreeKernel (rp parameters r) 1)
        (-fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 3 0)
          (fullNegativeKernelAction (rp parameters r) angular cell
            (radialRotatedCovariantKernel parameters L compact state r small positive) input) +
         fullNegativeKernelAction (rp parameters r) angular cell
          (radialRetainedForceKernel parameters L compact state r)
          (fullNegativeKernelAction (rp parameters r) angular cell
            (radialCovariantKernel parameters L compact state r small positive) input) + xiRadial)) =
      fullNegativeKernelAction (rp parameters r) angular cell (highAngularKernel (rp parameters r) 1) source ↔
    fullNegativeKernelAction (rp parameters r) angular cell (highAngularKernel (rp parameters r) 1) xiRadial =
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialRetainedFirstRowKernel parameters L compact state r small positive) input +
      fullNegativeKernelAction (rp parameters r) angular cell (highAngularKernel (rp parameters r) 1) source := by
  rw [highAngular_action_meanFree_eq, radialRetainedFirstRowKernel_action]
  simp only [map_add, map_neg, map_sub]
  constructor
  · intro equation
    rw [← equation]
    abel
  · intro equation
    rw [equation]
    abel

end Grad.AnnularReconstruction
