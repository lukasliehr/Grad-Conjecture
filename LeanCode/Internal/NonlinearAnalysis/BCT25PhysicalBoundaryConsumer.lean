import BCT24EvaluatedSourceConsumer
import BKC32PhysicalReconstructionConsumer

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.RealFixedRanges

/-- The actual reconstruction used by the physical boundary has exactly
the prescribed full mean-free flux. Its input is the original sourceRange,
and the normed p carrier stores its genuine angular derivative. -/
theorem physicalBoundaryReconstruction_correctedFlux
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : PhysicalBoundaryState parameters L compact) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2)
    (p : MeanFreeBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    actualCorrectedFluxTrace parameters L state.val.rho state.val.epsilon state.val.field
      state.val.coefficientSmall angular cell
      (actualPhysicalCovariantTrace parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.val.small
        state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
        angular cell p.val xi source.val)
      (positiveToNegative parameters angular cell xi) =
        meanFreeBoundaryPrimitiveTrace parameters angular cell p :=
  actualPhysicalCovariantTrace_correctedFlux_eq parameters L compact state.val angular cell large
    (meanFreeBoundaryPrimitiveTrace parameters angular cell p) p.val
    (meanFreeBoundaryPrimitiveTrace_meanFree parameters angular cell p)
    (meanFreeBoundaryPrimitive_derivative parameters angular cell p) xi source

/-- Joint physical consumer: the same reconstructed current has the exact
AF corrected flux, the actual AD19 high boundary row, and the uniform AH22
bound in the genuine P_R output norm. -/
theorem actualPhysicalBoundary_consumer
    (parameters : PhaseParameters) (L compact : ℝ) (positive : 0 < L)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : PhysicalBoundaryState parameters L compact)
        (p : MeanFreeBoundaryPrimitive parameters angular cell)
        (xi : PositiveTrace parameters angular cell 1)
        (source : sourceRange parameters (angular + cell + 2) large),
      let current := actualPhysicalCovariantTrace parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.val.small
        state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
        angular cell p.val xi source.val
      let boundary := physicalBoundaryFromPrescribedSource parameters L state.val.rho state.val.alpha
        state.val.delta state.val.parameter state.val.epsilon compact state.val.field state.property
        state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
        angular cell large p xi source
      actualCorrectedFluxTrace parameters L state.val.rho state.val.epsilon state.val.field
          state.val.coefficientSmall angular cell current (positiveToNegative parameters angular cell xi) =
        meanFreeBoundaryPrimitiveTrace parameters angular cell p ∧
      highBoundaryPrimitiveTrace parameters angular cell boundary =
        fullNegativeKernelAction parameters angular cell (highAngularKernel parameters 1)
          (fullNegativeKernelAction parameters angular cell
            (actualBoundaryMultiplier parameters L state.val.rho state.val.alpha state.val.delta
              state.val.parameter state.val.epsilon compact state.val.field state.val.compactNonnegative
              state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall) current) ∧
      ‖boundary‖ ^ 2 ≤ constant ^ 2 *
        (1 + physicalBudget parameters state.val.field state.val.rho state.val.epsilon (angular + cell + 8)) ^ 2 *
        (‖p‖ ^ 2 + 3 * ‖xi‖ ^ 2 + sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source.val‖ ^ 2) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    physicalBoundaryFromPrescribedSource_uniform_bound_sq parameters L compact positive angular cell large
  refine ⟨constant, nonnegative, ?_⟩
  intro state p xi source
  refine ⟨physicalBoundaryReconstruction_correctedFlux parameters L compact state angular cell large p xi source,
    ?_, ?_⟩
  · exact physicalBoundaryFromPrescribedSource_eq_covector parameters L state.val.rho state.val.alpha
      state.val.delta state.val.parameter state.val.epsilon compact state.val.field state.property
      state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
      angular cell large p xi source
  · exact bound state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon
      state.val.field state.property state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
      state.val.parameterSmall p xi source

end Grad.ActualBoundaryPrimitives
