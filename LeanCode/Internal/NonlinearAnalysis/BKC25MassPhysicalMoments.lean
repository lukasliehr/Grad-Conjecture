import BKC24SigmaPhysicalMoments

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem actualKnownJStarKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualKnownJStarKernel
  dsimp only
  with_reducible repeat' first
    | exact actualSigmaBoundaryKernel_physicalMoments parameters L compactRadius 
    | exact actualRotatedSigmaBoundaryKernel_physicalMoments parameters L compactRadius 
    | exact actualSigmaComponentBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedSigmaComponentBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualUnknownUKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownVKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply PhysicalKernelMoments.comp

theorem actualMassPerturbationKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualMassPerturbationKernel
  dsimp only
  with_reducible repeat' first
    | exact actualSigmaBoundaryKernel_physicalMoments parameters L compactRadius 
    | exact actualRotatedSigmaBoundaryKernel_physicalMoments parameters L compactRadius 
    | exact actualSigmaComponentBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedSigmaComponentBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualUnknownUKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownVKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply PhysicalKernelMoments.comp

theorem actualMassInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualMassInverseKernel
  dsimp only
  apply UniformKernelMoments.negativeIdentityInverse BoundaryReconstructionState.one_le_size
  exact actualMassPerturbationKernel_physicalMoments parameters L compactRadius

 theorem actualRecoveredMassKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualRecoveredMassKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualRecoveredMassKernel actualMassRightHandKernel
  apply PhysicalKernelMoments.comp
  · exact actualMassInverseKernel_physicalMoments parameters L compactRadius
  · apply UniformKernelMoments.sub
    · exact PhysicalKernelMoments.fixed parameters L compactRadius _
    · exact actualKnownJStarKernel_physicalMoments parameters L compactRadius

end Grad.BoundaryKernelAction
