import AHW3NormalizedEightSlotElimination

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

/-- Literal reference entries are independent of radial phase bookkeeping. -/
theorem sameCircularRetainedFirstRowKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularRetainedFirstRowKernel first L) (circularRetainedFirstRowKernel second L) := by
  unfold circularRetainedFirstRowKernel circularRetainedForceKernel
  exact (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularNormalizedRotatedCovariantKernel first second L)).sub
      (((sameConstantMatrixKernel _ _ _ _ _).smul 2).comp (sameCircularNormalizedCovariantKernel first second L)))

theorem sameCircularEliminationRightHandKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminationRightHandKernel first L) (circularEliminationRightHandKernel second L) := by
  unfold circularEliminationRightHandKernel
  exact (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (((sameConstantMatrixKernel _ _ _ _ _).sub
      ((sameCircularRetainedFirstRowKernel first second L).comp (sameConstantMatrixKernel _ _ _ _ _))).sub
        (sameConstantMatrixKernel _ _ _ _ _))

theorem sameCircularEliminatedXKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminatedXKernel first L) (circularEliminatedXKernel second L) :=
  ((sameScalarModeDiagonalKernel _ _ _ _ _ _).neg).comp (sameCircularEliminationRightHandKernel first second L)

theorem retainedFixedHighMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : ℕ) :
    RetainedPhysicalMoments parameters L compact (fun _ r => highAngularKernel (radialKernelParameters parameters r) dimension) :=
  RetainedPhysicalMoments.restrict (radialFixedHighMoments parameters L compact dimension)

theorem retainedEightSlotMoments (parameters : PhaseParameters) (L compact : ℝ) (slot : Fin 8) :
    RetainedPhysicalMoments parameters L compact (fun _ r => eightInputSlotKernel (radialKernelParameters parameters r) slot) :=
  RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem retainedKnownEightMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (fun _ r => knownEightToSevenKernel (radialKernelParameters parameters r)) :=
  RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem retainedNormalizedFirstRow_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact
      (fun state r => radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
      (fun _ r => circularRetainedFirstRowKernel (radialKernelParameters parameters r) L) :=
  RetainedDeviationMoments.restrict (radialNormalizedRetainedFirstRowKernel_referenceDifference parameters L compact)

theorem radialEliminationRightHandKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminationRightHandKernel parameters L compact)
      (fun _ r => circularEliminationRightHandKernel (radialKernelParameters parameters r) L) := by
  apply RetainedReferenceDifference.left (retainedFixedHighMoments parameters L compact 1)
  exact ((RetainedReferenceDifference.refl parameters L compact
    (fun _ r => eightInputSlotKernel (radialKernelParameters parameters r) 0)).sub
      ((retainedNormalizedFirstRow_referenceDifference parameters L compact).right
        (retainedKnownEightMoments parameters L compact))).sub
          (RetainedReferenceDifference.refl parameters L compact
            (fun _ r => eightInputSlotKernel (radialKernelParameters parameters r) 7))

theorem radialEliminationRightHandKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialEliminationRightHandKernel parameters L compact) :=
  (radialEliminationRightHandKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularEliminationRightHandKernel _ _ L))

theorem retainedInverse_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialRetainedHighInverse parameters L compact)
      (fun _ r => fullKernelNeg (retainedBInverseKernel (radialKernelParameters parameters r))) := by
  have equality (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
      fullKernelSub (radialRetainedHighInverse parameters L compact state r)
        (fullKernelNeg (retainedBInverseKernel (radialKernelParameters parameters r))) =
      fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
        (retainedBInverseKernel (radialKernelParameters parameters r)) := by
    apply FullTwoFrequencyKernel.ext_entry
    intro shift mode
    simp only [fullKernelSub_entry, fullKernelNeg_entry, fullKernelAdd_entry, sub_neg_eq_add]
  simpa only [RetainedReferenceDifference, equality] using radialRetainedHighInverse_referenceMoments parameters L compact

theorem radialEliminatedXKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminatedXKernel parameters L compact)
      (fun _ r => circularEliminatedXKernel (radialKernelParameters parameters r) L) :=
  (retainedInverse_referenceDifference parameters L compact).comp
    (radialEliminationRightHandKernel_referenceDifference parameters L compact)
    (radialEliminationRightHandKernel_physicalMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameScalarModeDiagonalKernel _ _ _ _ _ _).neg))

theorem radialEliminatedXKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialEliminatedXKernel parameters L compact) :=
  (radialEliminatedXKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularEliminatedXKernel _ _ L))

theorem radialEliminatedSevenKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminatedSevenKernel parameters L compact)
      (fun _ r => circularEliminatedSevenKernel (radialKernelParameters parameters r) L) :=
  (RetainedReferenceDifference.left (RetainedPhysicalMoments.restrict (radialFixedInjectionMoments parameters L compact 7 0))
    (radialEliminatedXKernel_referenceDifference parameters L compact)).add
      (RetainedReferenceDifference.refl parameters L compact (fun _ r => knownEightToSevenKernel (radialKernelParameters parameters r)))

theorem radialEliminatedSevenKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialEliminatedSevenKernel parameters L compact) :=
  ((RetainedPhysicalMoments.restrict (radialFixedInjectionMoments parameters L compact 7 0)).comp
    (radialEliminatedXKernel_physicalMoments parameters L compact)).add (retainedKnownEightMoments parameters L compact)

end Grad.AnnularReconstruction
