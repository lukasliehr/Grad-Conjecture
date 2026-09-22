import BCI20OriginalSourceBoundaryLift

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

def boundaryRetainedVector (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) : NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell (retainedTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell input)

def boundarySourceVector (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) : NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell (sourceTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell input)

/-- Exact AI1/AI9 extraction on every completed seven-slot input. -/
theorem sevenSlot_actual_block_decomposition (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) :
    sevenSlotFlatten parameters angular cell input =
      fullNegativeKernelAction parameters angular cell (coordinateInjectionKernel parameters 7 0) (input 0) +
      fullNegativeKernelAction parameters angular cell (retainedTupleInsertionKernel parameters) (boundaryRetainedVector parameters angular cell input) +
      fullNegativeKernelAction parameters angular cell (sourceTupleInsertionKernel parameters) (boundarySourceVector parameters angular cell input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [negativeTraceCoefficient_add, retainedTupleInsertionKernel, sourceTupleInsertionKernel,
    boundaryRetainedVector, boundarySourceVector, retainedTupleProjectionKernel, sourceTupleProjectionKernel,
    constantMatrixKernel_action_coefficient, retainedTupleInsertion_apply, retainedTupleProjection_apply,
    sourceTupleInsertion_apply, sourceTupleProjection_apply]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply]
  rw [coordinateInjectionKernel_action_coefficient]
  fin_cases coordinate <;> simp [sevenSlotFlatten_coefficient]

theorem boundarySourceVector_actual (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    boundarySourceVector parameters angular cell (actualSevenSlotTrace parameters L angular cell x xi source) =
      originalSourceBoundaryVector parameters L angular cell source := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  unfold boundarySourceVector sourceTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, sourceTupleProjection_apply, originalSourceBoundaryVector_coefficient]
  apply PiLp.ext
  intro coordinate
  have first := actualSevenSlotTrace_components parameters L angular cell x xi source
  have second := actualSevenSlotTrace_components parameters L angular cell 0 0 source
  fin_cases coordinate <;> simp [sevenSlotFlatten_coefficient, congrFun first, congrFun second]

theorem boundaryRetainedVector_actual_coefficient (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (boundaryRetainedVector parameters angular cell (actualSevenSlotTrace parameters L angular cell x xi source)) mode =
      WithLp.toLp 2 ![
        negativeTraceCoefficient parameters angular cell (positiveRotationToNegative parameters angular cell xi) mode 0,
        negativeTraceCoefficient parameters angular cell (positiveCellToNegative parameters angular cell xi) mode 0,
        negativeTraceCoefficient parameters angular cell (positiveToNegative parameters angular cell xi) mode 0] := by
  unfold boundaryRetainedVector retainedTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, retainedTupleProjection_apply]
  apply PiLp.ext
  intro coordinate
  have components := actualSevenSlotTrace_components parameters L angular cell x xi source
  fin_cases coordinate <;> simp [sevenSlotFlatten_coefficient, congrFun components]

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem actualPhysicalBoundary_block_equation (state : PhysicalBoundaryState parameters L compact) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) (high : IsHighAngularTrace parameters angular cell (input 0)) :
    fullSevenSlotKernelAction parameters angular cell state.physicalRow input =
      fullNegativeKernelAction parameters angular cell state.boundaryT (input 0) +
      fullNegativeKernelAction parameters angular cell (actualBoundaryN state) (boundaryRetainedVector parameters angular cell input) +
      fullNegativeKernelAction parameters angular cell (actualBoundaryH state) (boundarySourceVector parameters angular cell input) := by
  change fullNegativeKernelAction parameters angular cell state.physicalRow (sevenSlotFlatten parameters angular cell input) = _
  rw [sevenSlot_actual_block_decomposition, map_add, map_add]
  have fixed := highAngularKernel_fixed parameters angular cell (input 0) high
  unfold PhysicalBoundaryState.boundaryT actualBoundaryN actualBoundaryH
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  rw [fixed]

end Grad.ActualBoundaryInverse
