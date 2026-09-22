import AHQ9ActualFirstSystemContinuity
import AHP28RadialSigmaPhysicalMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- Reuse the actual state/radius-uniform moment estimates rather than
re-estimating physical coefficient families for continuity. -/
theorem regularKernelFamily_of_physicalMoments (parameters : PhaseParameters) (L compact : ℝ)
    {src tgt : ℕ}
    (family : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r src tgt)
    (moments : RadialPhysicalMoments parameters L compact family)
    (state : AnnularReconstructionState parameters L compact)
    (entries : ∀ shift input, Continuous (fun r => (family state r).entry shift input)) :
    RegularKernelFamily (family state) := by
  refine ⟨entries, fun moment => ?_⟩
  obtain ⟨C, C0, bound⟩ := moments moment
  exact ⟨C * state.size moment, mul_nonneg C0 (state.val.size_nonnegative moment), bound state⟩

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)

theorem radialRotatedSigmaKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialRotatedSigmaKernel parameters L compact state.val r 0) := by
  refine regularKernelFamily_of_physicalMoments parameters L compact _
    (radialRotatedSigmaKernel_physicalMoments parameters L compact) state ?_
  intro shift input
  refine rowMultiplicationEntry_continuous (X := RadialPoint) 3
    (fun r component mode => angularCoefficientSequence
      (radialSigmaCoefficients parameters L compact state.val r component 0) mode) ?_ shift input
  intro component mode
  exact continuous_const.mul (radialSigmaCoefficients_continuous parameters L compact state.val component 0 mode)

theorem radialSigmaComponentKernel_regular (component : Fin 3) :
    RegularKernelFamily (fun r : RadialPoint => radialSigmaComponentKernel parameters L compact state.val r component) := by
  refine regularKernelFamily_of_physicalMoments parameters L compact _
    (radialSigmaComponentKernel_physicalMoments parameters L compact component) state ?_
  intro shift input
  exact (radialSigmaCoefficients_continuous parameters L compact state.val component 0 shift).smul continuous_const

theorem radialRotatedSigmaComponentKernel_regular (component : Fin 3) :
    RegularKernelFamily (fun r : RadialPoint => radialRotatedSigmaComponentKernel parameters L compact state.val r component) := by
  refine regularKernelFamily_of_physicalMoments parameters L compact _
    (radialRotatedSigmaComponentKernel_physicalMoments parameters L compact component) state ?_
  intro shift input
  exact (continuous_const.mul (radialSigmaCoefficients_continuous parameters L compact state.val component 0 shift)).smul continuous_const

end Grad.AnnularKernelContinuity
