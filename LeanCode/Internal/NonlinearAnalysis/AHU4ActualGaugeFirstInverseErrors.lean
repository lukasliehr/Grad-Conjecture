import AHU3OrderedReferenceDifferences

noncomputable section
set_option maxHeartbeats 600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Internal proof tactic for the already accepted regular factors. -/
macro "ahu_regular" "(" p:term "," l:term "," c:term ")" : tactic => `(tactic|
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments $p $l $c
    | exact radialNegativeGammaInverseKernel_physicalMoments $p $l $c
    | exact radialEncodedFirstInverseKernel_physicalMoments $p $l $c
    | exact radialKnownEncodedDataKernel_physicalMoments $p $l $c
    | exact radialKnownWKernel_physicalMoments $p $l $c
    | exact radialKnownAStarKernel_physicalMoments $p $l $c
    | exact radialKnownRAStarKernel_physicalMoments $p $l $c
    | exact radialUnknownNKernel_physicalMoments $p $l $c
    | exact radialUnknownWKernel_physicalMoments $p $l $c
    | exact radialUnknownUKernel_physicalMoments $p $l $c
    | exact radialUnknownVKernel_physicalMoments $p $l $c
    | exact radialMassInverseKernel_physicalMoments $p $l $c
    | exact radialFixedFirstMoments $p $l $c
    | exact radialFixedSecondMoments $p $l $c
    | exact radialFixedThirdMoments $p $l $c
    | exact radialFixedJMoments $p $l $c
    | exact radialFixedRJMoments $p $l $c
    | exact radialFixedQAMoments $p $l $c
    | exact radialFixedD0Moments $p $l $c
    | exact radialFixedMeanMoments $p $l $c _
    | exact radialFixedMeanFreeMoments $p $l $c _
    | exact radialFixedSlotMoments $p $l $c _
    | exact radialFixedTwiceMoments $p $l $c _
    | exact radialFixedScaledSlotMoments $p $l $c _
    | apply UniformRadialKernelMoments.add
    | apply UniformRadialKernelMoments.sub
    | apply UniformRadialKernelMoments.neg
    | apply RadialPhysicalMoments.comp)

/-- Internal proof tactic keeps one actual coefficient deviation in every product. -/
syntax "ahu_vanishing" "(" term "," term "," term ")" : tactic
macro_rules
  | `(tactic| ahu_vanishing ($p, $l, $c)) => `(tactic|
      with_reducible first
      | exact radialForceKernel_vanishingMoments $p $l $c _
      | exact radialRotatedForceKernel_vanishingMoments $p $l $c _
      | exact radialGaugeRowsKernel_vanishingMoments $p $l $c
      | exact radialSigmaKernel_vanishingMoments $p $l $c
      | exact radialRotatedSigmaKernel_vanishingMoments $p $l $c
      | exact radialSigmaComponentKernel_vanishingMoments $p $l $c _
      | exact radialRotatedSigmaComponentKernel_vanishingMoments $p $l $c _
      | (apply UniformRadialKernelMoments.add <;> ahu_vanishing ($p, $l, $c))
      | (apply UniformRadialKernelMoments.neg; ahu_vanishing ($p, $l, $c))
      | (apply RadialDeviationMoments.regular_comp
         · solve | ahu_regular ($p, $l, $c)
         · ahu_vanishing ($p, $l, $c))
      | (apply RadialDeviationMoments.comp_regular
         · ahu_vanishing ($p, $l, $c)
         · solve | ahu_regular ($p, $l, $c)))

theorem radialGaugeCorrectionKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialGaugeCorrectionKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialGaugeCorrectionKernel radialGaugeMeanRowsKernel
  apply RadialDeviationMoments.regular_comp
  · exact RadialPhysicalMoments.fixed parameters L compact _
      (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  · ahu_vanishing (parameters, L, compact)

theorem radialGaugeQKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialGaugeQKernel parameters L compact state.val r state.gaugeSmall)
      (fun _ r => fullIdentityKernel (radialKernelParameters parameters r) 3) := by
  have bound := (RadialReferenceDifference.refl parameters L compact
    (fun _ r => fullIdentityKernel (radialKernelParameters parameters r) 3)).add
      (RadialReferenceDifference.zero (radialGaugeCorrectionKernel_vanishingMoments parameters L compact))
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

theorem radialEncodedPerturbationKernel_vanishingMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialEncodedPerturbationKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialEncodedPerturbationKernel radialEncodedE0Kernel radialEncodedE1Kernel
    radialEncodedE2Kernel radialGaugeDecodedKernel
  ahu_vanishing (parameters, L, compact)

theorem radialEncodedFirstSystemKernel_referenceDifference
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialEncodedFirstSystemKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => encodedD0Kernel (radialKernelParameters parameters r)) := by
  have bound := (RadialReferenceDifference.refl parameters L compact
    (fun _ r => encodedD0Kernel (radialKernelParameters parameters r))).add
      (RadialReferenceDifference.zero (radialEncodedPerturbationKernel_vanishingMoments parameters L compact))
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

theorem radialEncodedFirstInverseKernel_referenceDifference
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialEncodedFirstInverseKernel parameters L compact state.val r state.firstSmall)
      (fun _ r => encodedD0InverseKernel (radialKernelParameters parameters r)) := by
  apply (radialEncodedFirstSystemKernel_referenceDifference parameters L compact).inverse
    (radialEncodedFirstInverseKernel_physicalMoments parameters L compact)
    (radialFixedD0Moments parameters L compact)
  · intro state r
    exact (radialEncodedFirstInverseKernel_twoSided parameters L compact state.val r state.firstSmall).2
  · intro state r
    exact encodedD0Kernel_inverse_right _

end Grad.AnnularReconstruction
