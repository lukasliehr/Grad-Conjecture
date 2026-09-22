import AHW14ActualKVReferenceEstimate

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

theorem retainedNormalizedCovariantMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact
      (fun state r => radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property) :=
  RetainedPhysicalMoments.restrict (radialNormalizedCovariantKernel_physicalMoments parameters L compact)

theorem retainedNormalizedRotatedMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact
      (fun state r => radialNormalizedRotatedCovariantKernel parameters L compact state.val.val r state.val.property) :=
  RetainedPhysicalMoments.restrict (radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact)

theorem retainedNormalizedCovariantDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact
      (fun state r => radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property)
      (fun _ r => circularNormalizedCovariantKernel (radialKernelParameters parameters r) L) :=
  RetainedDeviationMoments.restrict (radialNormalizedCovariantKernel_referenceDifference parameters L compact)

theorem retainedNormalizedRotatedDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact
      (fun state r => radialNormalizedRotatedCovariantKernel parameters L compact state.val.val r state.val.property)
      (fun _ r => circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters r) L) :=
  RetainedDeviationMoments.restrict (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact)

theorem radialNormalizedCKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedCKernel parameters L compact)
      (fun _ r => circularNormalizedCKernel (radialKernelParameters parameters r) L) := by
  have first := (radialCofactorJetRowKernel_vanishingMoments parameters L compact 2 0 1).comp_regular
    (retainedNormalizedCovariantMoments parameters L compact)
  have second := (radialSignedCofactorRowKernel_referenceDifference parameters L compact 2).comp
    (retainedNormalizedRotatedDifference parameters L compact) (retainedNormalizedRotatedMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).neg))
  have third := (radialCofactorJetComponentKernel_vanishingMoments parameters L compact 1 2 0 1).comp_regular
    (retainedFixedSlotMoments parameters L compact 3)
  have fourth := (radialSignedCofactorComponentKernel_offDiagonal_vanishing parameters L compact 1 2 (by decide)).comp_regular
    (retainedFixedSlotMoments parameters L compact 1)
  have difference := RetainedReferenceDifference.left (retainedFixedHighMoments parameters L compact 1)
    ((((RetainedReferenceDifference.zero first).add second).add (RetainedReferenceDifference.zero third)).add
      (RetainedReferenceDifference.zero fourth))
  apply difference.congr (fun _ _ => rfl)
  intro state r
  apply congrArg (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1))
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelAdd_entry, fullZeroKernel_entry, zero_add, add_zero]

theorem radialKappaTwoSlot_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
        (sevenInputSlotKernel (radialKernelParameters parameters r) 1))
      (fun _ r => fullKernelNeg (sevenInputSlotKernel (radialKernelParameters parameters r) 1)) := by
  have difference := (radialSignedCofactorComponentKernel_referenceDifference parameters L compact 1 1).right
    (retainedFixedSlotMoments parameters L compact 1)
  apply difference.congr (fun _ _ => rfl)
  intro state r
  change fullKernelComposition (fullKernelNeg (fullIdentityKernel (radialKernelParameters parameters r) 1))
    (sevenInputSlotKernel (radialKernelParameters parameters r) 1) = _
  rw [fullKernelComposition_neg_outer, fullIdentityKernel_comp_rect]

/-- The displayed radial and axial coefficient derivatives have one vanishing budget. -/
theorem radialNormalizedRVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedRVKernel parameters L compact)
      (fun _ r => circularNormalizedRVKernel (radialKernelParameters parameters r) L) := by
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
  have difference := RetainedReferenceDifference.left (retainedFixedHighMoments parameters L compact 1)
    ((leading.sub (RetainedReferenceDifference.zero radialTerm)).sub (RetainedReferenceDifference.zero axialTerm))
  apply difference.congr (fun _ _ => rfl)
  intro state r
  simp only [fullKernel_sub_zero]
  rfl

theorem sameCircularNormalizedCKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedCKernel first L) (circularNormalizedCKernel second L) :=
  (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (((sameConstantMatrixKernel _ _ _ _ _).neg).comp (sameCircularNormalizedRotatedCovariantKernel first second L))

theorem sameCircularNormalizedRVKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedRVKernel first L) (circularNormalizedRVKernel second L) :=
  (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (((sameConstantMatrixKernel _ _ _ _ _).neg).add
      (((sameConstantMatrixKernel _ _ _ _ _).smul 2).comp (sameCircularNormalizedCovariantKernel first second L)))

theorem radialNormalizedCKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedCKernel parameters L compact) :=
  (radialNormalizedCKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedCKernel _ _ L))

theorem radialNormalizedRVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedRVKernel parameters L compact) :=
  (radialNormalizedRVKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedRVKernel _ _ L))

end Grad.AnnularReconstruction
