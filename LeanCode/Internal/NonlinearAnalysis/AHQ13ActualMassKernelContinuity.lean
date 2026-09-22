import AHQ12ActualUnknownKernelContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)

theorem radialKnownJStarKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialKnownJStarKernel parameters L compact state.val r state.firstSmall) := by
  have free := fixedRadialKernel_regular parameters (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have slot (component : Fin 7) := fixedRadialKernel_regular parameters (fun p => sevenInputSlotKernel p component) (fun p q => sameConstantMatrixKernel p q _ _ _)
  have first := ((radialRotatedSigmaKernel_regular parameters L compact state).comp
    (radialKnownAStarKernel_regular parameters L compact state)).add
    ((radialSigmaKernel_regular parameters L compact state.val 0).comp
      (radialKnownRAStarKernel_regular parameters L compact state))
  have second := ((radialRotatedSigmaComponentKernel_regular parameters L compact state 1).comp (slot 3)).add
    ((radialSigmaComponentKernel_regular parameters L compact state 1).comp (slot 1))
  exact free.comp (first.add second)

theorem radialMassPerturbationKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialMassPerturbationKernel parameters L compact state.val r state.firstSmall) := by
  have free := fixedRadialKernel_regular parameters (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  exact free.comp
    (((radialRotatedSigmaKernel_regular parameters L compact state).comp
      (radialUnknownUKernel_regular parameters L compact state)).add
      ((radialSigmaKernel_regular parameters L compact state.val 0).comp
        (radialUnknownVKernel_regular parameters L compact state)))

theorem radialMassInverseKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialMassInverseKernel parameters L compact state.val r state.property) :=
  (radialMassPerturbationKernel_regular parameters L compact state).negativeInverse
    (identityRadialKernel_regular parameters 1) (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialMassPerturbationKernel_small parameters L compact state.val r state.property)

theorem radialRecoveredMassKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialRecoveredMassKernel parameters L compact state.val r state.property) := by
  have slot := fixedRadialKernel_regular parameters (fun p => sevenInputSlotKernel p 0) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (radialMassInverseKernel_regular parameters L compact state).comp
    (slot.sub (radialKnownJStarKernel_regular parameters L compact state))

/-- The same normalized AH20 kernels, on every radius of the closed unit
interval, have continuous entries and uniform moments of every order. -/
theorem radialNormalizedCovariantKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialNormalizedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownUKernel_regular parameters L compact state).comp
    (radialRecoveredMassKernel_regular parameters L compact state)).add
    (radialKnownAStarKernel_regular parameters L compact state)

theorem radialNormalizedRotatedCovariantKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownVKernel_regular parameters L compact state).comp
    (radialRecoveredMassKernel_regular parameters L compact state)).add
    (radialKnownRAStarKernel_regular parameters L compact state)

end Grad.AnnularKernelContinuity
