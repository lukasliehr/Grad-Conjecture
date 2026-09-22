import BCI22ExactRetainedBoundaryFormula

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges

variable {parameters : PhaseParameters} {L compact : ℝ}

def originalSourceBoundaryPrimitive (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) : MeanFreeBoundaryPrimitive parameters angular cell :=
  ⟨originalSourceBoundaryLift state angular cell source, (originalSourceBoundaryLift_high state angular cell source).meanFree⟩

/-- The exact prescribed-source P_R physical boundary vanishes after the
actual BS33 source contribution, on the full original sourceRange. -/
theorem originalSourceBoundaryLift_PR_zero (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2) (source : sourceRange parameters (angular + cell + 2) large) :
    physicalBoundaryFromPrescribedSource parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
      state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
      angular cell large (originalSourceBoundaryPrimitive state angular cell source.val) 0 source = 0 := by
  apply Subtype.ext
  exact originalSourceBoundaryLift_equation state angular cell source.val

/-- The vanishing boundary is the actual projected AD19 covector applied
to the actual reconstructed covariant, not an independent boundary row. -/
theorem originalSourceBoundaryLift_physical_zero (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2) (source : sourceRange parameters (angular + cell + 2) large) :
    actualHighPhysicalBoundary parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
      state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
      angular cell (actualSevenSlotTrace parameters L angular cell (originalSourceBoundaryLift state angular cell source.val) 0 source.val) = 0 := by
  have physical := physicalBoundaryFromPrescribedSource_eq_high parameters L state.val.val.rho state.val.val.alpha state.val.val.delta
    state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.property
    state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall
    angular cell large (originalSourceBoundaryPrimitive state angular cell source.val) 0 source
  rw [originalSourceBoundaryLift_PR_zero] at physical
  simpa only [originalSourceBoundaryPrimitive, highBoundaryPrimitiveTrace, ZeroMemClass.coe_zero, map_zero] using physical.symm

/-- BS33's source value is exactly -T_a^{-1}H_a s(1), in the same complete
carrier used by AI11. This identity does not set the source term to zero. -/
theorem originalSourceBoundaryLift_exact_BS33 (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    originalSourceBoundaryLiftOnHigh state angular cell source =
      actualSourceBoundaryTerm state angular cell (originalSourceBoundaryVector parameters L angular cell source) := by
  apply Subtype.ext
  exact (actualSourceBoundaryTerm_kernel state angular cell _).symm

/-- Original-domain source consumer with the evaluated physical budget. -/
theorem originalSourceBoundaryLift_prescribed_bound (parameters : PhaseParameters) (L compact : ℝ) (positive : 0 < L)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : BoundaryInverseState parameters L compact,
      ∀ source : sourceRange parameters (angular + cell + 2) large,
      ‖originalSourceBoundaryLiftOnHigh state angular cell source.val‖ ≤
        constant * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (angular + cell + 8)) * ‖source‖ := by
  obtain ⟨constant, nonnegative, bound⟩ := originalSourceBoundaryLift_bound parameters L compact positive angular cell
  exact ⟨constant, nonnegative, fun state source => bound state source.val⟩

end Grad.ActualBoundaryInverse
