import AHU5ExactCircularEncodedData

noncomputable section
set_option maxHeartbeats 2200000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

def circularKnownWKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition (encodedD0InverseKernel parameters) (circularKnownEncodedDataKernel parameters L)

def circularKnownAStarKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd (fullKernelComposition (encodedJKernel parameters) (circularKnownWKernel parameters L))
    (fullKernelComposition (secondCoordinateInjectionKernel parameters) (sevenInputSlotKernel parameters 3))

def circularKnownRAStarKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd (fullKernelComposition (encodedRotationKernel parameters) (circularKnownWKernel parameters L))
    (fullKernelComposition (secondCoordinateInjectionKernel parameters) (sevenInputSlotKernel parameters 1))

def circularUnknownWKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelComposition (encodedD0InverseKernel parameters) (circularUnknownNKernel parameters)

def circularUnknownUKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelAdd (fullKernelComposition (encodedJKernel parameters) (circularUnknownWKernel parameters))
    (actualUnknownQAKernel parameters)

def circularUnknownVKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelAdd (fullKernelComposition (encodedRotationKernel parameters) (circularUnknownWKernel parameters))
    (firstCoordinateInjectionKernel parameters)

theorem circularKnownWKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularKnownWKernel (radialKernelParameters parameters r) L) := by
  unfold circularKnownWKernel circularKnownEncodedDataKernel
  ahu_regular (parameters, L, compact)

theorem circularKnownAStarKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularKnownAStarKernel (radialKernelParameters parameters r) L) := by
  unfold circularKnownAStarKernel circularKnownWKernel circularKnownEncodedDataKernel
  ahu_regular (parameters, L, compact)

theorem circularKnownRAStarKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularKnownRAStarKernel (radialKernelParameters parameters r) L) := by
  unfold circularKnownRAStarKernel circularKnownWKernel circularKnownEncodedDataKernel
  ahu_regular (parameters, L, compact)

theorem circularUnknownWKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularUnknownWKernel (radialKernelParameters parameters r)) := by
  unfold circularUnknownWKernel circularUnknownNKernel
  ahu_regular (parameters, L, compact)

theorem circularUnknownUKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularUnknownUKernel (radialKernelParameters parameters r)) := by
  unfold circularUnknownUKernel circularUnknownWKernel circularUnknownNKernel
  ahu_regular (parameters, L, compact)

theorem circularUnknownVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularUnknownVKernel (radialKernelParameters parameters r)) := by
  unfold circularUnknownVKernel circularUnknownWKernel circularUnknownNKernel
  ahu_regular (parameters, L, compact)

theorem radialKnownWKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialKnownWKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularKnownWKernel (radialKernelParameters parameters r) L) := by
  exact (radialEncodedFirstInverseKernel_referenceDifference parameters L compact).comp
    (radialKnownEncodedDataKernel_referenceDifference parameters L compact)
    (radialKnownEncodedDataKernel_physicalMoments parameters L compact)
    (radialFixedD0Moments parameters L compact)

theorem radialUnknownWKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialUnknownWKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularUnknownWKernel (radialKernelParameters parameters r)) := by
  exact (radialEncodedFirstInverseKernel_referenceDifference parameters L compact).comp
    (radialUnknownNKernel_referenceDifference parameters L compact)
    (radialUnknownNKernel_physicalMoments parameters L compact)
    (radialFixedD0Moments parameters L compact)

/-- Gauging adds a vanishing correction to the original chart. -/
theorem radialGaugeQKernel_comp_referenceDifference {parameters : PhaseParameters} {L compact : ℝ}
    {input : ℕ}
    {actual reference : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input 3}
    (difference : RadialReferenceDifference parameters L compact actual reference)
    (regular : RadialPhysicalMoments parameters L compact actual) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelComposition
        (radialGaugeQKernel parameters L compact state.val r state.gaugeSmall) (actual state r)) reference := by
  have bound := (radialGaugeQKernel_referenceDifference parameters L compact).comp difference regular
    (RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameFullIdentityKernel _ _ _))
  apply bound.congr (fun _ _ => rfl)
  intro state r
  exact fullIdentityKernel_comp_rect _ _

theorem radialKnownAStarKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialKnownAStarKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularKnownAStarKernel (radialKernelParameters parameters r) L) := by
  unfold radialKnownAStarKernel circularKnownAStarKernel
  apply radialGaugeQKernel_comp_referenceDifference
  · exact (RadialReferenceDifference.left (radialFixedJMoments parameters L compact)
      (radialKnownWKernel_referenceDifference parameters L compact)).add
        (RadialReferenceDifference.refl parameters L compact _)
  · ahu_regular (parameters, L, compact)

theorem radialUnknownUKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialUnknownUKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularUnknownUKernel (radialKernelParameters parameters r)) := by
  unfold radialUnknownUKernel circularUnknownUKernel
  apply radialGaugeQKernel_comp_referenceDifference
  · exact (RadialReferenceDifference.left (radialFixedJMoments parameters L compact)
      (radialUnknownWKernel_referenceDifference parameters L compact)).add
        (RadialReferenceDifference.refl parameters L compact _)
  · ahu_regular (parameters, L, compact)

theorem radialKnownRAStarKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialKnownRAStarKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularKnownRAStarKernel (radialKernelParameters parameters r) L) := by
  unfold radialKnownRAStarKernel circularKnownRAStarKernel radialKnownRotatedQStarKernel
  exact (RadialReferenceDifference.left (radialFixedRJMoments parameters L compact)
      (radialKnownWKernel_referenceDifference parameters L compact)).add
        (RadialReferenceDifference.refl parameters L compact _)

theorem radialUnknownVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialUnknownVKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => circularUnknownVKernel (radialKernelParameters parameters r)) := by
  unfold radialUnknownVKernel circularUnknownVKernel
  exact (RadialReferenceDifference.left (radialFixedRJMoments parameters L compact)
      (radialUnknownWKernel_referenceDifference parameters L compact)).add
        (RadialReferenceDifference.refl parameters L compact _)

end Grad.AnnularReconstruction
