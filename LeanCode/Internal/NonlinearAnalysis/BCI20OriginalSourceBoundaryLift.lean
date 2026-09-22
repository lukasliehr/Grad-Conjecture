import BCI19OriginalSourceTuple

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges

theorem fullNegativeKernelAction_zero {input output : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (fullZeroKernel parameters input output) field = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  have summation := fullNegativeKernelAction_coefficient_hasSum parameters angular cell (fullZeroKernel parameters input output) field mode
  rw [← summation.tsum_eq]
  simp [fullZeroKernel_entry, negativeTraceCoefficient]

variable {parameters : PhaseParameters} {L compact : ℝ}

/-- Literal original-source BS33 value, -T_a^{-1}H_a s(1). -/
def originalSourceBoundaryLift (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) : NegativeTrace parameters angular cell 1 :=
  fullNegativeKernelAction parameters angular cell (actualSourceBoundaryLiftKernel state)
    (originalSourceBoundaryVector parameters L angular cell source)

theorem originalSourceBoundaryLift_high (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    IsHighAngularTrace parameters angular cell (originalSourceBoundaryLift state angular cell source) :=
  highKernelAction parameters angular cell _ (actualSourceBoundaryLift_high state) _

/-- The source boundary contribution lies in the complete original high
negative-half carrier, retaining its inherited physical norm. -/
def originalSourceBoundaryLiftOnHigh (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) : HighBoundaryPrimitive parameters angular cell :=
  ⟨originalSourceBoundaryLift state angular cell source, originalSourceBoundaryLift_high state angular cell source⟩

theorem originalSourceBoundaryLift_equation (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    fullSevenSlotKernelAction parameters angular cell state.val.physicalRow
      (actualSevenSlotTrace parameters L angular cell (originalSourceBoundaryLift state angular cell source) 0 source) = 0 := by
  let data := originalSourceBoundaryVector parameters L angular cell source
  have exactKernel := congrArg (fun kernel : FullTwoFrequencyKernel parameters 3 1 =>
    fullNegativeKernelAction parameters angular cell kernel data) (actualSourceBoundaryLift_equation state)
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_zero] at exactKernel
  have high := highAngularKernel_fixed parameters angular cell (originalSourceBoundaryLift state angular cell source)
    (originalSourceBoundaryLift_high state angular cell source)
  have xRow : fullNegativeKernelAction parameters angular cell state.val.boundaryT
      (originalSourceBoundaryLift state angular cell source) =
      fullNegativeKernelAction parameters angular cell state.val.physicalRow
        (fullNegativeKernelAction parameters angular cell (coordinateInjectionKernel parameters 7 0)
          (originalSourceBoundaryLift state angular cell source)) := by
    unfold PhysicalBoundaryState.boundaryT
    simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
    rw [high]
  change fullNegativeKernelAction parameters angular cell state.val.boundaryT
      (originalSourceBoundaryLift state angular cell source) +
    fullNegativeKernelAction parameters angular cell (actualBoundaryH state.val) data = 0 at exactKernel
  rw [xRow, actualBoundaryH, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] at exactKernel
  change fullNegativeKernelAction parameters angular cell state.val.physicalRow
    (sevenSlotFlatten parameters angular cell (actualSevenSlotTrace parameters L angular cell
      (originalSourceBoundaryLift state angular cell source) 0 source)) = 0
  rw [originalSevenSlot_source_split, map_add]
  exact exactKernel

theorem originalSourceBoundaryLift_bound (parameters : PhaseParameters) (L compact : ℝ) (positive : 0 < L)
    (angular cell : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : BoundaryInverseState parameters L compact,
      ∀ source : ZAmbient parameters (angular + cell + 2),
      ‖originalSourceBoundaryLift state angular cell source‖ ≤
        constant * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (angular + cell + 8)) * ‖source‖ := by
  obtain ⟨base, baseNonnegative, bound⟩ := actualSourceBoundaryLift_physicalMoments parameters L compact (angular + cell + 1)
  let projection := fullKernelMoment parameters (angular + cell + 1) (sourceTupleProjectionKernel parameters) *
    |sourceOuterTraceConstant L (angular + cell)|
  have projectionNonnegative : 0 ≤ projection :=
    mul_nonneg (fullKernelMoment_nonnegative parameters _ _) (abs_nonneg _)
  refine ⟨base * projection, mul_nonneg baseNonnegative projectionNonnegative, ?_⟩
  intro state source
  apply (fullNegativeKernelAction_bound parameters angular cell (actualSourceBoundaryLiftKernel state) _).trans
  have estimate := mul_le_mul (bound state) (originalSourceBoundaryVector_bound parameters L positive angular cell source)
    (norm_nonneg _) (mul_nonneg baseNonnegative (state.val.val.size_nonnegative _))
  exact estimate.trans_eq (by
    change base * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (angular + cell + 1 + 7)) *
      (projection * ‖source‖) = _
    rw [show angular + cell + 1 + 7 = angular + cell + 8 by omega]
    ring)

end Grad.ActualBoundaryInverse
