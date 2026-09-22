import BCT18UniformBoundaryCoefficients
import BCT21TotalPhysicalBoundary
import BKC26CovariantPhysicalMoments

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem actualHighPhysicalBoundaryKernel_uniformMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryKernelMoments parameters L compact
      (fun state => actualHighPhysicalBoundaryKernel parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.property state.val.compactNonnegative
        state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall) := by
  unfold actualHighPhysicalBoundaryKernel
  apply BoundaryKernelMoments.comp
  · exact BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1)
  · exact BoundaryKernelMoments.comp
      (actualBoundaryMultiplier_uniformMoments parameters L compact)
      (BoundaryKernelMoments.of_reconstruction (actualCovariantKernel_physicalMoments parameters L compact))

/-- The actual AH21 moment has exactly one high physical coefficient factor
B(t+7). Ordered composition uses the accepted high/low + low/high inequality. -/
theorem actualDifferentiatedPhysicalBoundaryKernel_uniformMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryKernelMoments parameters L compact
      (fun state => actualDifferentiatedPhysicalBoundaryKernel parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.property state.val.compactNonnegative
        state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall) := by
  unfold actualDifferentiatedPhysicalBoundaryKernel
  apply BoundaryKernelMoments.comp
  · exact BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1)
  · apply UniformKernelMoments.add
    · exact BoundaryKernelMoments.comp
        (actualRotatedBoundaryMultiplier_uniformMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualCovariantKernel_physicalMoments parameters L compact))
    · exact BoundaryKernelMoments.comp
        (actualBoundaryMultiplier_uniformMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualRotatedCovariantKernel_physicalMoments parameters L compact))

theorem actualExtendedPhysicalBoundaryKernel_uniformMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryKernelMoments parameters L compact
      (fun state => actualExtendedPhysicalBoundaryKernel parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.property state.val.compactNonnegative
        state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall) := by
  unfold actualExtendedPhysicalBoundaryKernel
  exact BoundaryKernelMoments.comp
    (BoundaryKernelMoments.fixed parameters L compact (angularInverseKernel parameters 1))
    (actualDifferentiatedPhysicalBoundaryKernel_uniformMoments parameters L compact)

end Grad.ActualBoundaryPrimitives
