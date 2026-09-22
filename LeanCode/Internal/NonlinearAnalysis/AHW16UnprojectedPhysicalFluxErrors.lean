import AHW15NormalizedFluxReferenceErrors

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

def radialNormalizedUnprojectedCKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelAdd
      (fullKernelAdd
        (fullKernelAdd
          (fullKernelComposition (radialCofactorJetRowKernel parameters L compact state 2 0 1 r)
            (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property))
          (fullKernelComposition (radialSignedCofactorRowKernel parameters L compact state 2 r)
            (radialNormalizedRotatedCovariantKernel parameters L compact state.val.val r state.val.property)))
        (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 2 0 1 r)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 3)))
      (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
        (sevenInputSlotKernel (radialKernelParameters parameters r) 1))

def radialNormalizedUnprojectedRVKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelSub
      (fullKernelSub
        (fullKernelAdd
          (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
            (sevenInputSlotKernel (radialKernelParameters parameters r) 1))
          (fullKernelComposition (radialKVKernel parameters L compact state r)
            (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property)))
        (fullKernelSmul (r.val : ℂ)
          (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 0 1 0 r)
            (sevenInputSlotKernel (radialKernelParameters parameters r) 3))))
      (fullKernelSmul ((r.val : ℂ) * (L : ℂ)⁻¹)
        (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 2 0 2 r)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 3)))

def circularNormalizedUnprojectedCKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (fullKernelNeg (coordinateProjectionKernel parameters 3 2))
      (circularNormalizedRotatedCovariantKernel parameters L)

def circularNormalizedUnprojectedRVKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelAdd (fullKernelNeg (sevenInputSlotKernel parameters 1))
      (fullKernelComposition (fullKernelSmul 2 (coordinateProjectionKernel parameters 3 0))
        (circularNormalizedCovariantKernel parameters L))

theorem radialNormalizedCKernel_projected (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    radialNormalizedCKernel parameters L compact state r =
      fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (radialNormalizedUnprojectedCKernel parameters L compact state r) := rfl

theorem radialNormalizedRVKernel_projected (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    radialNormalizedRVKernel parameters L compact state r =
      fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (radialNormalizedUnprojectedRVKernel parameters L compact state r) := rfl

theorem radialNormalizedUnprojectedCKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedUnprojectedCKernel parameters L compact)
      (fun _ r => circularNormalizedUnprojectedCKernel (radialKernelParameters parameters r) L) := by
  have first := (radialCofactorJetRowKernel_vanishingMoments parameters L compact 2 0 1).comp_regular
    (retainedNormalizedCovariantMoments parameters L compact)
  have second := (radialSignedCofactorRowKernel_referenceDifference parameters L compact 2).comp
    (retainedNormalizedRotatedDifference parameters L compact) (retainedNormalizedRotatedMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).neg))
  have third := (radialCofactorJetComponentKernel_vanishingMoments parameters L compact 1 2 0 1).comp_regular
    (retainedFixedSlotMoments parameters L compact 3)
  have fourth := (radialSignedCofactorComponentKernel_offDiagonal_vanishing parameters L compact 1 2 (by decide)).comp_regular
    (retainedFixedSlotMoments parameters L compact 1)
  have difference := (((RetainedReferenceDifference.zero first).add second).add (RetainedReferenceDifference.zero third)).add
      (RetainedReferenceDifference.zero fourth)
  apply difference.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [circularNormalizedUnprojectedCKernel, fullKernelAdd_entry, fullZeroKernel_entry, zero_add, add_zero]

theorem radialNormalizedUnprojectedRVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedUnprojectedRVKernel parameters L compact)
      (fun _ r => circularNormalizedUnprojectedRVKernel (radialKernelParameters parameters r) L) := by
  have leading := (radialKappaTwoSlot_referenceDifference parameters L compact).add
    ((radialKVKernel_referenceDifference parameters L compact).comp
      (retainedNormalizedCovariantDifference parameters L compact) (retainedNormalizedCovariantMoments parameters L compact)
      (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul 2)))
  have radialTerm := ((radialCofactorJetComponentKernel_vanishingMoments parameters L compact 1 0 1 0).comp_regular
    (retainedFixedSlotMoments parameters L compact 3)).smul_bounded (fun r => (r.val : ℂ)) 1 (by norm_num) radialPoint_norm_le_one
  have axialTerm := ((radialCofactorJetComponentKernel_vanishingMoments parameters L compact 1 2 0 2).comp_regular
    (retainedFixedSlotMoments parameters L compact 3)).smul_bounded (fun r => (r.val : ℂ) * (L : ℂ)⁻¹)
      ‖(L : ℂ)⁻¹‖ (norm_nonneg _) (fun r => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (radialPoint_norm_le_one r) (norm_nonneg _)).trans_eq (one_mul _))
  have difference := (leading.sub (RetainedReferenceDifference.zero radialTerm)).sub (RetainedReferenceDifference.zero axialTerm)
  apply difference.congr (fun _ _ => rfl)
  intro state r
  simp only [fullKernel_sub_zero]
  rfl

theorem sameCircularNormalizedUnprojectedCKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedUnprojectedCKernel first L) (circularNormalizedUnprojectedCKernel second L) :=
  ((sameConstantMatrixKernel _ _ _ _ _).neg).comp (sameCircularNormalizedRotatedCovariantKernel first second L)

theorem sameCircularNormalizedUnprojectedRVKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedUnprojectedRVKernel first L) (circularNormalizedUnprojectedRVKernel second L) :=
  ((sameConstantMatrixKernel _ _ _ _ _).neg).add
    (((sameConstantMatrixKernel _ _ _ _ _).smul 2).comp (sameCircularNormalizedCovariantKernel first second L))

theorem radialNormalizedUnprojectedCKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedUnprojectedCKernel parameters L compact) :=
  (radialNormalizedUnprojectedCKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedUnprojectedCKernel _ _ L))

theorem radialNormalizedUnprojectedRVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedUnprojectedRVKernel parameters L compact) :=
  (radialNormalizedUnprojectedRVKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedUnprojectedRVKernel _ _ L))

end Grad.AnnularReconstruction
