import BKC21GaugePhysicalMoments

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem actualEncodedPerturbationKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualEncodedPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.gaugeSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualEncodedPerturbationKernel actualEncodedE0Kernel actualEncodedE1Kernel
    actualEncodedE2Kernel actualGaugeDecodedKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply PhysicalKernelMoments.comp

 theorem actualPreconditionedEncodedPerturbationKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualPreconditionedEncodedPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.gaugeSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualPreconditionedEncodedPerturbationKernel
  exact PhysicalKernelMoments.comp
    (PhysicalKernelMoments.fixed parameters L compactRadius _)
    (actualEncodedPerturbationKernel_physicalMoments parameters L compactRadius)

 theorem actualEncodedIdentityInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualEncodedIdentityInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualEncodedIdentityInverseKernel
  dsimp only
  apply UniformKernelMoments.neg
  apply UniformKernelMoments.negativeIdentityInverse BoundaryReconstructionState.one_le_size
  exact (actualPreconditionedEncodedPerturbationKernel_physicalMoments
    parameters L compactRadius).neg

 theorem actualEncodedFirstInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualEncodedFirstInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualEncodedFirstInverseKernel
  exact PhysicalKernelMoments.comp
    (actualEncodedIdentityInverseKernel_physicalMoments parameters L compactRadius)
    (PhysicalKernelMoments.fixed parameters L compactRadius _)

end Grad.BoundaryKernelAction
