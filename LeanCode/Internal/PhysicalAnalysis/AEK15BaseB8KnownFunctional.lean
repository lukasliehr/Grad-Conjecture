import AEK14GraphKnownDataConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularUniformBoundary Grad.AnnularCurrentEnergy
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

section Base

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

theorem reconstructionSize_zero_le_one :
    state.val.val.size 0 ≤ state.val.val.size 1 := by
  unfold BoundaryReconstructionState.size
  exact add_le_add le_rfl
    (physicalBudget_monotone parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (by norm_num : 7 ≤ 8))

/-- BF13's literal base-grade coefficient.  Every physical coefficient factor
uses `size 1 = 1 + B8`; the source factor uses only the two genuine radial
graph norms. -/
def actualHighGraphKnownB8Size
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower 0)
    (datum : HighBoundaryPrimitive parameters 0 0) : ℝ :=
  5 * (4 * eliminatedBulkConstant parameters L compact 0 *
      state.val.val.size 1 * ‖known‖ + 3 * ‖auxiliary‖) +
    uniformOuterTraceConstant L *
      (knownBoundaryInverseConstant parameters L compact 1 *
          state.val.val.size 1 * ‖datum‖ +
        graphSourceLiftMomentConstant parameters L compact 1 *
          state.val.val.size 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖))

theorem actualHighGraphKnownB8Size_nonnegative
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower 0)
    (datum : HighBoundaryPrimitive parameters 0 0) :
    0 ≤ actualHighGraphKnownB8Size parameters L compact lower state
      known auxiliary graphs datum := by
  have sizeOne := state.val.val.size_nonnegative 1
  unfold actualHighGraphKnownB8Size
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (eliminatedBulkConstant_nonnegative parameters L compact 0)) sizeOne)
        (norm_nonneg known))
      (mul_nonneg (by norm_num) (norm_nonneg auxiliary))))
    (mul_nonneg (uniformOuterTraceConstant_nonnegative L) (add_nonneg
      (mul_nonneg (mul_nonneg
        (knownBoundaryInverseConstant_nonnegative parameters L compact 1) sizeOne)
        (norm_nonneg datum))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (graphSourceLiftMomentConstant_nonnegative parameters L compact 1)
              sizeOne)
            (fullKernelMoment_nonnegative parameters 1 _))
          uniformSourceOuterConstant_nonnegative)
        (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg graphs.1))
          (norm_nonneg graphs.2)))))

theorem actualHighGraphKnownFunctionalSize_base_le_B8
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower 0)
    (datum : HighBoundaryPrimitive parameters 0 0) :
    actualHighGraphKnownFunctionalSize parameters L compact lower state 0 0
      known auxiliary graphs datum ≤
      actualHighGraphKnownB8Size parameters L compact lower state
        known auxiliary graphs datum := by
  have bulk :
      4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 *
          ‖known‖ ≤
        4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1 *
          ‖known‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (reconstructionSize_zero_le_one parameters L compact state)
        (mul_nonneg (by norm_num)
          (eliminatedBulkConstant_nonnegative parameters L compact 0)))
      (norm_nonneg known)
  unfold actualHighGraphKnownFunctionalSize actualHighGraphKnownB8Size
  simpa only [zero_add, Nat.reduceAdd, RetainedInverseState.outerInverseState,
    RetainedInverseState.boundaryState] using
    add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add bulk le_rfl) (by norm_num)) le_rfl

/-- BF13 at the actual base grade: the zero-incoming known functional is
uniform in the collar and costs only the literal physical B8 coefficient. -/
theorem ActualHighGraphKnownData.zeroFunctional_norm_base_B8
    (data : ActualHighGraphKnownData parameters lower 0 0) :
    ‖data.zeroFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state 0 0‖ ≤
      actualHighGraphKnownB8Size parameters L compact lower state
        data.weighted data.auxiliary data.graphs data.datum := by
  exact (data.zeroFunctional_norm parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state 0 0).trans
      (actualHighGraphKnownFunctionalSize_base_le_B8 parameters L compact lower
        state data.weighted data.auxiliary data.graphs data.datum)

/-- The B8 normalization is literal, rather than a renamed abstract size. -/
theorem actualHighGraphKnownB8Size_literal
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower 0)
    (datum : HighBoundaryPrimitive parameters 0 0) :
    actualHighGraphKnownB8Size parameters L compact lower state
      known auxiliary graphs datum =
    5 * (4 * eliminatedBulkConstant parameters L compact 0 *
        (1 + physicalBudget parameters state.val.val.field state.val.val.rho
          state.val.val.epsilon 8) * ‖known‖ + 3 * ‖auxiliary‖) +
      uniformOuterTraceConstant L *
        (knownBoundaryInverseConstant parameters L compact 1 *
            (1 + physicalBudget parameters state.val.val.field state.val.val.rho
              state.val.val.epsilon 8) * ‖datum‖ +
          graphSourceLiftMomentConstant parameters L compact 1 *
            (1 + physicalBudget parameters state.val.val.field state.val.val.rho
              state.val.val.epsilon 8) *
            fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖)) := by
  rfl

end Base
end Grad.AnnularCurrentSource
