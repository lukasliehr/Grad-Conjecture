import AHU6CircularChartReconstruction

noncomputable section
set_option maxHeartbeats 2200000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

theorem radialKnownJStarKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialKnownJStarKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialKnownJStarKernel
  ahu_vanishing (parameters, L, compact)

theorem radialMassPerturbationKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialMassPerturbationKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialMassPerturbationKernel
  ahu_vanishing (parameters, L, compact)

theorem radialMassSystemKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialMassPerturbationKernel parameters L compact state.val r state.firstSmall))
      (fun _ r => fullKernelNeg (fullIdentityKernel (radialKernelParameters parameters r) 1)) := by
  have bound := (RadialReferenceDifference.zero
    (radialMassPerturbationKernel_vanishingMoments parameters L compact)).sub
      (RadialReferenceDifference.refl parameters L compact
        (fun _ r => fullIdentityKernel (radialKernelParameters parameters r) 1))
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

theorem radialMassInverseKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialMassInverseKernel parameters L compact state.val r state.property)
      (fun _ r => fullKernelNeg (fullIdentityKernel (radialKernelParameters parameters r) 1)) := by
  apply (radialMassSystemKernel_referenceDifference parameters L compact).inverse
    (radialMassInverseKernel_physicalMoments parameters L compact)
    (UniformRadialKernelMoments.neg
      (RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameFullIdentityKernel _ _ _)))
  · intro state r
    exact (radialMassInverseKernel_twoSided parameters L compact state.val r state.property).2
  · intro state r
    rw [fullKernelComposition_neg_outer, fullKernelComposition_neg_inner, fullIdentityKernel_comp]
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    simp

def circularRecoveredMassKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (fullKernelNeg (fullIdentityKernel parameters 1)) (sevenInputSlotKernel parameters 0)

theorem radialMassRightHandKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialMassRightHandKernel parameters L compact state.val r state.property)
      (fun _ r => sevenInputSlotKernel (radialKernelParameters parameters r) 0) :=
  RadialReferenceDifference.sub_right _ (radialKnownJStarKernel_vanishingMoments parameters L compact)

theorem radialMassRightHandKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialMassRightHandKernel parameters L compact state.val r state.property) := by
  exact (radialFixedSlotMoments parameters L compact 0).sub
    (radialKnownJStarKernel_physicalMoments parameters L compact)

theorem radialRecoveredMassKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialRecoveredMassKernel parameters L compact state.val r state.property)
      (fun _ r => circularRecoveredMassKernel (radialKernelParameters parameters r)) := by
  exact (radialMassInverseKernel_referenceDifference parameters L compact).comp
    (radialMassRightHandKernel_referenceDifference parameters L compact)
    (radialMassRightHandKernel_physicalMoments parameters L compact)
    (UniformRadialKernelMoments.neg
      (RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameFullIdentityKernel _ _ _)))

end Grad.AnnularReconstruction
