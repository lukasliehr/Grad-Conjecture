import AIQ3OriginalWeakRowConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse Grad.AnnularCurrentSource

theorem boundaryRetainedVector_sevenSlot (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    boundaryRetainedVector parameters angular cell (sevenSlotTrace parameters angular cell x xi source) =
      originalRetainedBoundaryVector parameters L angular cell xi := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  unfold originalRetainedBoundaryVector
  rw [boundaryRetainedVector_actual_coefficient]
  unfold boundaryRetainedVector retainedTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, retainedTupleProjection_apply]
  rfl

theorem boundarySourceVector_sevenSlot (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    boundarySourceVector parameters angular cell (sevenSlotTrace parameters angular cell x xi source) =
      graphSourceBoundaryVector parameters angular cell source := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  unfold boundarySourceVector graphSourceBoundaryVector sourceTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, constantMatrixKernel_action_coefficient,
    sourceTupleProjection_apply, sourceTupleProjection_apply]
  rfl

variable {parameters : PhaseParameters} {L compact : ℝ}

/-- The actual BCT13 physical boundary on the direct original seven-slot graph trace, at every grade. -/
def graphNativePhysicalBoundary (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (x : HighBoundaryPrimitive parameters angular cell) (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) : HighBoundaryPrimitive parameters angular cell :=
  actualPhysicalBoundaryPR parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
    state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
    state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
    angular cell (sevenSlotTrace parameters angular cell x.val xi source)

/-- Both literal angular conditions hold: x is high and Rxi is the genuine derivative of xi. -/
theorem graphNativePhysicalBoundary_eq_high (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (x : HighBoundaryPrimitive parameters angular cell) (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    highBoundaryPrimitiveTrace parameters angular cell (graphNativePhysicalBoundary state angular cell x xi source) =
      actualHighPhysicalBoundary parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
        state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
        state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
        angular cell (sevenSlotTrace parameters angular cell x.val xi source) := by
  apply actualPhysicalBoundaryPR_eq_high
  · exact x.property.meanFree
  · exact positiveToNegative_derivative parameters angular cell xi

/-- Exact original outer inverse equivalence, using the frozen T inverse on a genuine source tuple. -/
theorem graphNativePhysicalBoundary_inverse_iff (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (x datum : HighBoundaryPrimitive parameters angular cell) (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    graphNativePhysicalBoundary state angular cell x xi source = datum ↔
      x = actualRetainedBoundaryTerm state angular cell (originalRetainedBoundaryVector parameters L angular cell xi) +
        actualHighGraphBoundaryVector state angular cell datum source := by
  have decomposition := actualPhysicalBoundary_block_equation state.val angular cell
    (sevenSlotTrace parameters angular cell x.val xi source) x.property
  rw [boundaryRetainedVector_sevenSlot parameters L, boundarySourceVector_sevenSlot] at decomposition
  have block : graphNativePhysicalBoundary state angular cell x xi source =
      actualBoundaryTOnHigh state.val angular cell x +
        actualBoundaryNOnHigh state.val angular cell (originalRetainedBoundaryVector parameters L angular cell xi) +
        actualBoundaryHOnHigh state.val angular cell (graphSourceBoundaryVector parameters angular cell source) := by
    apply Subtype.ext
    exact decomposition
  rw [block, actualAI11_boundary_equivalence]
  rfl

end Grad.AnnularPhysicalSolution
