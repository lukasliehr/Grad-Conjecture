import AHU4ActualGaugeFirstInverseErrors

noncomputable section
set_option maxHeartbeats 2400000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Circular encoded data retain the independent ambient `RF0` slot 5. -/
def circularKnownEncodedDataKernel (parameters : PhaseParameters) (L : ℝ) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd
    (fullKernelComposition (firstCoordinateInjectionKernel parameters)
      (fullKernelComposition (angularMeanKernel parameters 1) (sevenInputSlotKernel parameters 4)))
    (fullKernelAdd
      (fullKernelComposition (secondCoordinateInjectionKernel parameters) (sevenInputSlotKernel parameters 5))
      (fullKernelComposition (thirdCoordinateInjectionKernel parameters)
        (fullKernelAdd (sevenInputSlotKernel parameters 6)
          (fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel parameters 2)))))

def circularUnknownNKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel parameters)
    (fullKernelSmul 2 (fullIdentityKernel parameters 1))

theorem circularKnownEncodedDataKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularKnownEncodedDataKernel (radialKernelParameters parameters r) L) := by
  unfold circularKnownEncodedDataKernel
  ahu_regular (parameters, L, compact)

theorem circularUnknownNKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularUnknownNKernel (radialKernelParameters parameters r)) := by
  unfold circularUnknownNKernel
  ahu_regular (parameters, L, compact)

theorem radialKnownEncodedDataKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialKnownEncodedDataKernel parameters L compact state.val r state.gaugeSmall)
      (fun _ r => circularKnownEncodedDataKernel (radialKernelParameters parameters r) L) := by
  unfold radialKnownEncodedDataKernel radialKnownD0Kernel radialKnownD1Kernel radialKnownD2Kernel
    circularKnownEncodedDataKernel
  apply RadialReferenceDifference.add
  · apply RadialReferenceDifference.left (radialFixedFirstMoments parameters L compact)
    apply RadialReferenceDifference.sub_right
    unfold radialKnownQStarKernel
    ahu_vanishing (parameters, L, compact)
  · apply RadialReferenceDifference.add
    · apply RadialReferenceDifference.left (radialFixedSecondMoments parameters L compact)
      apply RadialReferenceDifference.sub_right
      unfold radialKnownQStarKernel radialKnownRotatedQStarKernel
      ahu_vanishing (parameters, L, compact)
    · apply RadialReferenceDifference.left (radialFixedThirdMoments parameters L compact)
      apply RadialReferenceDifference.sub_right
      unfold radialKnownQStarKernel
      ahu_vanishing (parameters, L, compact)

theorem radialUnknownNKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialUnknownNKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularUnknownNKernel (radialKernelParameters parameters r)) := by
  have first : RadialDeviationMoments parameters L compact
      (fun state r => radialUnknownN0Kernel parameters L compact state.val r state.firstSmall) := by
    unfold radialUnknownN0Kernel radialUnknownGaugeQAKernel
    ahu_vanishing (parameters, L, compact)
  have third : RadialDeviationMoments parameters L compact
      (fun state r => radialUnknownN2Kernel parameters L compact state.val r state.firstSmall) := by
    unfold radialUnknownN2Kernel radialUnknownGaugeQAKernel
    ahu_vanishing (parameters, L, compact)
  have second : RadialReferenceDifference parameters L compact
      (fun state r => radialUnknownN1Kernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularUnknownNKernel (radialKernelParameters parameters r)) := by
    unfold radialUnknownN1Kernel circularUnknownNKernel
    apply RadialReferenceDifference.left (radialFixedSecondMoments parameters L compact)
    apply RadialReferenceDifference.sub_right
    unfold radialUnknownGaugeQAKernel
    ahu_vanishing (parameters, L, compact)
  have bound := (RadialReferenceDifference.zero first).add
    (second.add (RadialReferenceDifference.zero third))
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

end Grad.AnnularReconstruction
