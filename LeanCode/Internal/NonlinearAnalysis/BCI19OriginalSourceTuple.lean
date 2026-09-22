import BCI18CompleteHighInverseAndSource

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges

/-- The actual original completed endpoint tuple (F0,RF0,F2), extracted
from AH20; no extra independent source trace is introduced. -/
def originalSourceBoundaryVector (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) : NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell (sourceTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 0 source))

theorem originalSourceBoundaryVector_coefficient (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (originalSourceBoundaryVector parameters L angular cell source) mode =
      WithLp.toLp 2 ![
        negativeTraceCoefficient parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 0 source 4) mode 0,
        negativeTraceCoefficient parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 0 source 5) mode 0,
        negativeTraceCoefficient parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 0 source 6) mode 0] := by
  unfold originalSourceBoundaryVector sourceTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, sourceTupleProjection_apply]
  rfl

theorem originalSourceBoundaryVector_insertion (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    fullNegativeKernelAction parameters angular cell (sourceTupleInsertionKernel parameters)
      (originalSourceBoundaryVector parameters L angular cell source) =
      sevenSlotFlatten parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 0 source) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [sourceTupleInsertionKernel, constantMatrixKernel_action_coefficient, originalSourceBoundaryVector_coefficient,
    sourceTupleInsertion_apply]
  apply PiLp.ext
  intro coordinate
  rw [sevenSlotFlatten_coefficient]
  have components := actualSevenSlotTrace_components parameters L angular cell 0 0 source
  fin_cases coordinate <;> simp [congrFun components, negativeTraceCoefficient]

theorem originalSevenSlot_source_split (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (source : ZAmbient parameters (angular + cell + 2)) :
    sevenSlotFlatten parameters angular cell (actualSevenSlotTrace parameters L angular cell x 0 source) =
      fullNegativeKernelAction parameters angular cell (coordinateInjectionKernel parameters 7 0) x +
        fullNegativeKernelAction parameters angular cell (sourceTupleInsertionKernel parameters)
          (originalSourceBoundaryVector parameters L angular cell source) := by
  rw [originalSourceBoundaryVector_insertion]
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeTraceCoefficient_add]
  apply PiLp.ext
  intro coordinate
  rw [PiLp.add_apply, coordinateInjectionKernel_action_coefficient, sevenSlotFlatten_coefficient,
    sevenSlotFlatten_coefficient]
  have first := actualSevenSlotTrace_components parameters L angular cell x 0 source
  have second := actualSevenSlotTrace_components parameters L angular cell 0 0 source
  fin_cases coordinate <;> simp [congrFun first, congrFun second, negativeTraceCoefficient]

/-- The old exact AH18 source norm controls the new tuple by a fixed
coordinate projection, with no change of source domain. -/
theorem originalSourceBoundaryVector_bound (parameters : PhaseParameters) (L : ℝ) (positive : 0 < L) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    ‖originalSourceBoundaryVector parameters L angular cell source‖ ≤
      fullKernelMoment parameters (angular + cell + 1) (sourceTupleProjectionKernel parameters) *
        |sourceOuterTraceConstant L (angular + cell)| * ‖source‖ := by
  have inputBound := actualSevenSlotTrace_bound_sq parameters L positive angular cell 0 0 source
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add] at inputBound
  have input : ‖actualSevenSlotTrace parameters L angular cell 0 0 source‖ ≤
      |sourceOuterTraceConstant L (angular + cell)| * ‖source‖ := by
    have nonnegative := mul_nonneg (abs_nonneg (sourceOuterTraceConstant L (angular + cell))) (norm_nonneg source)
    nlinarith [sq_abs (sourceOuterTraceConstant L (angular + cell))]
  unfold originalSourceBoundaryVector
  apply (fullNegativeKernelAction_bound parameters angular cell (sourceTupleProjectionKernel parameters) _).trans
  rw [sevenSlotFlatten_norm]
  exact (mul_le_mul_of_nonneg_left input (fullKernelMoment_nonnegative parameters _ _)).trans_eq (mul_assoc _ _ _).symm

end Grad.ActualBoundaryInverse
