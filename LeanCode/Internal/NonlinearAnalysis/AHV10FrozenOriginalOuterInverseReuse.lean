import AHV9CompleteRetainedHighIsomorphism

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges
variable {parameters : PhaseParameters} {L compact : ℝ}

/-- Exact AI9–AI11 consumer on the original full sourceRange and complete
physical P_R datum. The datum's inherited coordinate is its genuine Rh.
No radial/cap inverse or coupled low/high solver is asserted here. -/
theorem retainedInverse_originalPhysicalBoundary_iff (state : RetainedInverseState parameters L compact) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2) (x datum : HighBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1) (source : sourceRange parameters (angular + cell + 2) large) :
    physicalBoundaryFromPrescribedSource parameters L state.boundaryState.val.rho state.boundaryState.val.alpha state.boundaryState.val.delta
      state.boundaryState.val.parameter state.boundaryState.val.epsilon compact state.boundaryState.val.field state.boundaryState.property
      state.boundaryState.val.compactNonnegative state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall state.boundaryState.val.parameterSmall
      angular cell large ⟨x.val, x.property.meanFree⟩ xi source = datum ↔
      x = actualRetainedBoundaryTerm state.outerInverseState angular cell (originalRetainedBoundaryVector parameters L angular cell xi) +
        (actualBoundaryInverseOnHigh state.outerInverseState angular cell datum + originalSourceBoundaryLiftOnHigh state.outerInverseState angular cell source.val) :=
  originalPhysicalBoundary_inverse_iff state.outerInverseState angular cell large x datum xi source

end Grad.AnnularReconstruction
