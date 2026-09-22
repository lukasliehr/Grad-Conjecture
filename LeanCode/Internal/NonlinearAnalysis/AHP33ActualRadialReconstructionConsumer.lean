import AHP31RadialMassPhysicalMoments

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- The literal original-slot derivative and corrected-flux identities at
all positive radii. These are reconstruction identities, before annular L2
realization and the remaining encoded force/gauge equivalence. -/
def OriginalRadialActionLaws (parameters : PhaseParameters) (L compact : ℝ) : Prop :=
  ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
    (positive : 0 < r.val) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell),
    (IsAngularMeanFree (radialKernelParameters parameters r) angular cell (input 0) →
      IsAngularDerivative (radialKernelParameters parameters r) angular cell (input 3) (input 1) →
      IsAngularDerivative (radialKernelParameters parameters r) angular cell
        (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
          (radialCovariantKernel parameters L compact state.val r state.property positive)
          (sevenSlotFlatten (radialKernelParameters parameters r) angular cell input))
        (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
          (radialRotatedCovariantKernel parameters L compact state.val r state.property positive)
          (sevenSlotFlatten (radialKernelParameters parameters r) angular cell input))) ∧
    (∀ (flux : NegativeTrace (radialKernelParameters parameters r) angular cell 1),
      IsAngularMeanFree (radialKernelParameters parameters r) angular cell flux →
      IsAngularDerivative (radialKernelParameters parameters r) angular cell flux (input 0) →
      IsAngularDerivative (radialKernelParameters parameters r) angular cell (input 3) (input 1) →
      radialCorrectedFluxTrace parameters L compact state.val r angular cell
        (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
          (radialCovariantKernel parameters L compact state.val r state.property positive)
          (sevenSlotFlatten (radialKernelParameters parameters r) angular cell input))
        ((r.val : ℂ)⁻¹ • input 3) = flux)

theorem originalRadialActionLaws (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalRadialActionLaws parameters L compact := by
  intro state r positive angular cell input
  exact ⟨radialCovariantKernel_derivative parameters L compact state.val r state.property
      positive angular cell input,
    radialCovariantKernel_correctedFlux_eq parameters L compact state.val r state.property
      positive angular cell input⟩

/-- One physical B7 neighborhood is fixed before all radii and all envelope
grades. The normalized kernels have one high factor; the physical action
retains the explicit reciprocal radius in its two scalar slots. -/
theorem actualRadialReconstructionConsumer (parameters : PhaseParameters) (L compact : ℝ) :
    0 < radialMassLowRadius parameters L compact ∧
    RadialPhysicalMoments parameters L compact
      (fun state r => radialNormalizedCovariantKernel parameters L compact state.val r state.property) ∧
    RadialPhysicalMoments parameters L compact
      (fun state r => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property) ∧
    OriginalRadialActionLaws parameters L compact :=
  ⟨radialMassLowRadius_positive parameters L compact,
    radialNormalizedCovariantKernel_physicalMoments parameters L compact,
    radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact,
    originalRadialActionLaws parameters L compact⟩

end Grad.AnnularReconstruction
