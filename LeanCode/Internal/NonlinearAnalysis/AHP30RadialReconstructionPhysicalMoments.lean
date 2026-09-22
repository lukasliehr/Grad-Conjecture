import AHP29RadialFirstInversePhysicalMoments

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem radialKnownEncodedDataKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialKnownEncodedDataKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialKnownEncodedDataKernel radialKnownD0Kernel radialKnownD1Kernel radialKnownD2Kernel radialKnownQStarKernel radialKnownRotatedQStarKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialKnownWKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialKnownWKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialKnownWKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialKnownAStarKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialKnownAStarKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialKnownAStarKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialKnownRAStarKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialKnownRAStarKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialKnownRAStarKernel radialKnownRotatedQStarKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialUnknownNKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialUnknownNKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialUnknownNKernel radialUnknownN0Kernel radialUnknownN1Kernel radialUnknownN2Kernel radialUnknownGaugeQAKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialUnknownWKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialUnknownWKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialUnknownWKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
    | exact radialKnownRAStarKernel_physicalMoments parameters L compact
    | exact radialUnknownNKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialUnknownUKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialUnknownUKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialUnknownUKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
    | exact radialKnownRAStarKernel_physicalMoments parameters L compact
    | exact radialUnknownNKernel_physicalMoments parameters L compact
    | exact radialUnknownWKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

theorem radialUnknownVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialUnknownVKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialUnknownVKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialEncodedFirstInverseKernel_physicalMoments parameters L compact
    | exact radialKnownEncodedDataKernel_physicalMoments parameters L compact
    | exact radialKnownWKernel_physicalMoments parameters L compact
    | exact radialKnownAStarKernel_physicalMoments parameters L compact
    | exact radialKnownRAStarKernel_physicalMoments parameters L compact
    | exact radialUnknownNKernel_physicalMoments parameters L compact
    | exact radialUnknownWKernel_physicalMoments parameters L compact
    | exact radialUnknownUKernel_physicalMoments parameters L compact
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
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp

end Grad.AnnularReconstruction
