import BCI24EvaluatedSourceOneHigh

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges

/-- The literal retained derivative tuple, independent of x and sources. -/
def originalRetainedBoundaryVector (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (xi : PositiveTrace parameters angular cell 1) : NegativeTrace parameters angular cell 3 :=
  boundaryRetainedVector parameters angular cell (actualSevenSlotTrace parameters L angular cell 0 xi 0)

theorem boundaryRetainedVector_actual (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    boundaryRetainedVector parameters angular cell (actualSevenSlotTrace parameters L angular cell x xi source) =
      originalRetainedBoundaryVector parameters L angular cell xi := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  unfold originalRetainedBoundaryVector
  rw [boundaryRetainedVector_actual_coefficient, boundaryRetainedVector_actual_coefficient]

variable {parameters : PhaseParameters} {L compact : ℝ}

/-- Exact AI9–AI11 consumer on the original full sourceRange and complete
physical P_R datum. The datum's inherited coordinate is its genuine Rh.
No radial/cap inverse or coupled low/high solver is asserted here. -/
theorem originalPhysicalBoundary_inverse_iff (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2) (x datum : HighBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1) (source : sourceRange parameters (angular + cell + 2) large) :
    physicalBoundaryFromPrescribedSource parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
      state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
      angular cell large ⟨x.val, x.property.meanFree⟩ xi source = datum ↔
      x = actualRetainedBoundaryTerm state angular cell (originalRetainedBoundaryVector parameters L angular cell xi) +
        (actualBoundaryInverseOnHigh state angular cell datum + originalSourceBoundaryLiftOnHigh state angular cell source.val) := by
  have decomposition := actualPhysicalBoundary_block_equation state.val angular cell
    (actualSevenSlotTrace parameters L angular cell x.val xi source.val) x.property
  rw [boundarySourceVector_actual, boundaryRetainedVector_actual] at decomposition
  have physicalBlock : physicalBoundaryFromPrescribedSource parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
      state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
      angular cell large ⟨x.val, x.property.meanFree⟩ xi source =
      actualBoundaryTOnHigh state.val angular cell x +
        actualBoundaryNOnHigh state.val angular cell (originalRetainedBoundaryVector parameters L angular cell xi) +
        actualBoundaryHOnHigh state.val angular cell (originalSourceBoundaryVector parameters L angular cell source.val) := by
    apply Subtype.ext
    exact decomposition
  rw [physicalBlock, actualAI11_boundary_equivalence, originalSourceBoundaryLift_exact_BS33]

end Grad.ActualBoundaryInverse
