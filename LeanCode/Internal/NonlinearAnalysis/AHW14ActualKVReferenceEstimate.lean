import AHW13LiteralCorrectedFluxKernels

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

theorem retainedFixedMeanFreeMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : ℕ) :
    RetainedPhysicalMoments parameters L compact
      (fun _ r => angularMeanFreeKernel (radialKernelParameters parameters r) dimension) :=
  RetainedPhysicalMoments.restrict (radialFixedMeanFreeMoments parameters L compact dimension)

theorem retainedFixedSlotMoments (parameters : PhaseParameters) (L compact : ℝ) (slot : Fin 7) :
    RetainedPhysicalMoments parameters L compact (fun _ r => sevenInputSlotKernel (radialKernelParameters parameters r) slot) :=
  RetainedPhysicalMoments.restrict (radialFixedSlotMoments parameters L compact slot)

theorem retainedForceMoments (parameters : PhaseParameters) (L compact : ℝ) (kind : Fin 2) :
    RetainedPhysicalMoments parameters L compact (fun state r => radialForceKernel parameters L compact state.val.val r kind 0) :=
  (RetainedDeviationMoments.restrict (radialForceKernel_vanishingMoments parameters L compact kind)).regular

theorem retainedForceOneMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (fun state r => radialRetainedForceKernel parameters L compact state.val.val r) := by
  have difference : RetainedReferenceDifference parameters L compact
      (fun state r => radialRetainedForceKernel parameters L compact state.val.val r)
      (fun _ r => circularRetainedForceKernel (radialKernelParameters parameters r)) :=
    RetainedDeviationMoments.restrict (radialRetainedForceKernel_referenceDifference parameters L compact)
  exact difference.actual_regular
    (RetainedPhysicalMoments.restrict (circularRetainedForceKernel_physicalMoments parameters L compact))

theorem radialSignedCofactorComponentKernel_offDiagonal (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (different : row ≠ column) (r : RadialPoint) :
    radialSignedCofactorComponentKernel parameters L compact state row column r =
      radialCofactorJetComponentKernel parameters L compact state row column 0 0 r := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp [radialSignedCofactorComponentKernel, circularCofactorComponentKernel, different]

theorem radialSignedCofactorComponentKernel_offDiagonal_vanishing (parameters : PhaseParameters) (L compact : ℝ)
    (row column : Fin 3) (different : row ≠ column) :
    RetainedDeviationMoments parameters L compact
      (fun state r => radialSignedCofactorComponentKernel parameters L compact state row column r) := by
  simpa only [radialSignedCofactorComponentKernel_offDiagonal parameters L compact _ row column different] using
    radialCofactorJetComponentKernel_vanishingMoments parameters L compact row column 0 0

theorem radialOriginalForceZeroKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialOriginalForceZeroKernel parameters L compact)
      (fun _ r => fullKernelSmul (-2) (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)) :=
  RetainedReferenceDifference.add_right _ (RetainedDeviationMoments.restrict (radialForceKernel_vanishingMoments parameters L compact 0))

theorem radialOriginalForceZeroKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialOriginalForceZeroKernel parameters L compact) :=
  (radialOriginalForceZeroKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul (-2)))

/-- In particular the density/force contribution has reference +2e_radial. -/
theorem radialKappaTwoForceZero_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
        (radialOriginalForceZeroKernel parameters L compact state r))
      (fun _ r => fullKernelSmul 2 (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)) := by
  have difference := (radialSignedCofactorComponentKernel_referenceDifference parameters L compact 1 1).comp
    (radialOriginalForceZeroKernel_referenceDifference parameters L compact)
    (radialOriginalForceZeroKernel_physicalMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularCofactorComponentKernel _ _ 1 1))
  apply difference.congr (fun _ _ => rfl)
  intro state r
  change fullKernelComposition (fullKernelNeg (fullIdentityKernel (radialKernelParameters parameters r) 1))
    (fullKernelSmul (-2) (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)) = _
  rw [fullKernelComposition_neg_outer, fullIdentityKernel_comp_rect]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelNeg_entry, fullKernelSmul_entry]
  module

/-- Uniform actual KV difference, retaining both noncommuting mean corrections. -/
theorem radialKVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialKVKernel parameters L compact)
      (fun _ r => fullKernelSmul 2 (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)) := by
  have first := (radialCofactorJetRowKernel_vanishingMoments parameters L compact 1 0 1).add
    ((radialSignedCofactorComponentKernel_offDiagonal_vanishing parameters L compact 1 0 (by decide)).comp_regular
      ((retainedFixedMeanFreeMoments parameters L compact 1).comp (retainedForceOneMoments parameters L compact)))
  have last := (radialSignedCofactorComponentKernel_offDiagonal_vanishing parameters L compact 1 2 (by decide)).comp_regular
    ((retainedFixedMeanFreeMoments parameters L compact 1).comp (retainedForceMoments parameters L compact 1))
  have difference := ((RetainedReferenceDifference.zero first).add
    (radialKappaTwoForceZero_referenceDifference parameters L compact)).sub (RetainedReferenceDifference.zero last)
  apply difference.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelSub_entry, fullKernelAdd_entry, fullZeroKernel_entry, zero_add, sub_zero]

theorem radialKVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialKVKernel parameters L compact) :=
  (radialKVKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul 2))

end Grad.AnnularReconstruction
