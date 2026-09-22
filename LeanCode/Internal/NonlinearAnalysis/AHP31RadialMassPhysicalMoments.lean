import AHP30RadialReconstructionPhysicalMoments

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem radialKnownJStarKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialKnownJStarKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialKnownJStarKernel
  with_reducible repeat' first
    | exact radialSigmaKernel_physicalMoments parameters L compact
    | exact radialRotatedSigmaKernel_physicalMoments parameters L compact
    | exact radialSigmaComponentKernel_physicalMoments parameters L compact 1
    | exact radialRotatedSigmaComponentKernel_physicalMoments parameters L compact 1
    | exact radialUnknownUKernel_physicalMoments parameters L compact
    | exact radialUnknownVKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
    | exact radialKnownRAStarKernel_physicalMoments parameters L compact
    | exact radialFixedFirstMoments parameters L compact
    | exact radialFixedSecondMoments parameters L compact
    | exact radialFixedThirdMoments parameters L compact
    | exact radialFixedJMoments parameters L compact
    | exact radialFixedRJMoments parameters L compact
    | exact radialFixedQAMoments parameters L compact
    | exact radialFixedD0Moments parameters L compact
    | exact radialFixedMeanMoments parameters L compact _
    | exact radialFixedMeanFreeMoments parameters L compact _
    | exact radialFixedSlotMoments parameters L compact _
    | exact radialFixedTwiceMoments parameters L compact _
    | exact radialFixedScaledSlotMoments parameters L compact _
    | apply UniformRadialKernelMoments.add
    | apply RadialPhysicalMoments.comp

theorem radialMassPerturbationKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialMassPerturbationKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialMassPerturbationKernel
  with_reducible repeat' first
    | exact radialSigmaKernel_physicalMoments parameters L compact
    | exact radialRotatedSigmaKernel_physicalMoments parameters L compact
    | exact radialSigmaComponentKernel_physicalMoments parameters L compact 1
    | exact radialRotatedSigmaComponentKernel_physicalMoments parameters L compact 1
    | exact radialUnknownUKernel_physicalMoments parameters L compact
    | exact radialUnknownVKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
    | exact radialKnownRAStarKernel_physicalMoments parameters L compact
    | exact radialFixedFirstMoments parameters L compact
    | exact radialFixedSecondMoments parameters L compact
    | exact radialFixedThirdMoments parameters L compact
    | exact radialFixedJMoments parameters L compact
    | exact radialFixedRJMoments parameters L compact
    | exact radialFixedQAMoments parameters L compact
    | exact radialFixedD0Moments parameters L compact
    | exact radialFixedMeanMoments parameters L compact _
    | exact radialFixedMeanFreeMoments parameters L compact _
    | exact radialFixedSlotMoments parameters L compact _
    | exact radialFixedTwiceMoments parameters L compact _
    | exact radialFixedScaledSlotMoments parameters L compact _
    | apply UniformRadialKernelMoments.add
    | apply RadialPhysicalMoments.comp

theorem radialMassInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialMassInverseKernel parameters L compact state.val r state.property) := by
  unfold radialMassInverseKernel
  apply UniformRadialKernelMoments.negativeIdentityInverse (fun state => state.val.one_le_size)
  exact radialMassPerturbationKernel_physicalMoments parameters L compact

theorem radialRecoveredMassKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialRecoveredMassKernel parameters L compact state.val r state.property) := by
  unfold radialRecoveredMassKernel radialMassRightHandKernel
  apply RadialPhysicalMoments.comp
  · exact radialMassInverseKernel_physicalMoments parameters L compact
  · apply UniformRadialKernelMoments.sub
    · exact radialFixedSlotMoments parameters L compact _
    · exact radialKnownJStarKernel_physicalMoments parameters L compact

theorem radialNormalizedCovariantKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialNormalizedCovariantKernel parameters L compact state.val r state.property) := by
  unfold radialNormalizedCovariantKernel
  apply UniformRadialKernelMoments.add
  · exact RadialPhysicalMoments.comp
      (radialUnknownUKernel_physicalMoments parameters L compact)
      (radialRecoveredMassKernel_physicalMoments parameters L compact)
  · exact radialKnownAStarKernel_physicalMoments parameters L compact

theorem radialNormalizedRotatedCovariantKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property) := by
  unfold radialNormalizedRotatedCovariantKernel
  apply UniformRadialKernelMoments.add
  · exact RadialPhysicalMoments.comp
      (radialUnknownVKernel_physicalMoments parameters L compact)
      (radialRecoveredMassKernel_physicalMoments parameters L compact)
  · exact radialKnownRAStarKernel_physicalMoments parameters L compact

end Grad.AnnularReconstruction
