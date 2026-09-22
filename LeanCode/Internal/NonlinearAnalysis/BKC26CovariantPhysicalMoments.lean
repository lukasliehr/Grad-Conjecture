import BKC25MassPhysicalMoments

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem actualCovariantKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualCovariantKernel
  dsimp only
  apply UniformKernelMoments.add
  · exact PhysicalKernelMoments.comp
      (actualUnknownUKernel_physicalMoments parameters L compactRadius)
      (actualRecoveredMassKernel_physicalMoments parameters L compactRadius)
  · exact actualKnownAStarKernel_physicalMoments parameters L compactRadius

theorem actualRotatedCovariantKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualRotatedCovariantKernel
  dsimp only
  apply UniformKernelMoments.add
  · exact PhysicalKernelMoments.comp
      (actualUnknownVKernel_physicalMoments parameters L compactRadius)
      (actualRecoveredMassKernel_physicalMoments parameters L compactRadius)
  · exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius

end Grad.BoundaryKernelAction
