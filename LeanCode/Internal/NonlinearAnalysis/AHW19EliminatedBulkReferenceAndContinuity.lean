import AHW18LiteralUnprojectedCircularRows

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity

theorem sameCircularEliminatedSevenKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminatedSevenKernel first L) (circularEliminatedSevenKernel second L) :=
  ((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularEliminatedXKernel first second L)).add
    (sameConstantMatrixKernel _ _ _ _ _)

theorem sameCircularEliminatedCKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminatedCKernel first L) (circularEliminatedCKernel second L) :=
  (sameCircularNormalizedCKernel first second L).comp (sameCircularEliminatedSevenKernel first second L)

theorem sameCircularEliminatedRVKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminatedRVKernel first L) (circularEliminatedRVKernel second L) :=
  (sameCircularNormalizedRVKernel first second L).comp (sameCircularEliminatedSevenKernel first second L)

theorem sameCircularEliminatedBulkKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularEliminatedBulkKernel first L) (circularEliminatedBulkKernel second L) :=
  (((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularEliminatedXKernel first second L)).add
    ((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularEliminatedCKernel first second L))).add
      ((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularEliminatedRVKernel first second L))

theorem radialEliminatedCKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminatedCKernel parameters L compact)
      (fun _ r => circularEliminatedCKernel (radialKernelParameters parameters r) L) :=
  (radialNormalizedCKernel_referenceDifference parameters L compact).comp
    (radialEliminatedSevenKernel_referenceDifference parameters L compact)
    (radialEliminatedSevenKernel_physicalMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedCKernel _ _ L))

theorem radialEliminatedRVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminatedRVKernel parameters L compact)
      (fun _ r => circularEliminatedRVKernel (radialKernelParameters parameters r) L) :=
  (radialNormalizedRVKernel_referenceDifference parameters L compact).comp
    (radialEliminatedSevenKernel_referenceDifference parameters L compact)
    (radialEliminatedSevenKernel_physicalMoments parameters L compact)
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedRVKernel _ _ L))

theorem radialEliminatedBulkKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialEliminatedBulkKernel parameters L compact)
      (fun _ r => circularEliminatedBulkKernel (radialKernelParameters parameters r) L) :=
  ((RetainedReferenceDifference.left (RetainedPhysicalMoments.restrict (radialFixedInjectionMoments parameters L compact 3 0))
    (radialEliminatedXKernel_referenceDifference parameters L compact)).add
      (RetainedReferenceDifference.left (RetainedPhysicalMoments.restrict (radialFixedInjectionMoments parameters L compact 3 1))
        (radialEliminatedCKernel_referenceDifference parameters L compact))).add
          (RetainedReferenceDifference.left (RetainedPhysicalMoments.restrict (radialFixedInjectionMoments parameters L compact 3 2))
            (radialEliminatedRVKernel_referenceDifference parameters L compact))

theorem radialEliminatedBulkKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialEliminatedBulkKernel parameters L compact) :=
  (radialEliminatedBulkKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L))

theorem radialNormalizedCKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialNormalizedCKernel parameters L compact state) :=
  (scalarModeRadialKernel_regular parameters _ _ _ _).comp
    (radialNormalizedUnprojectedCKernel_regular parameters L compact state)

theorem radialNormalizedRVKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialNormalizedRVKernel parameters L compact state) :=
  (scalarModeRadialKernel_regular parameters _ _ _ _).comp
    (radialNormalizedUnprojectedRVKernel_regular parameters L compact state)

theorem radialEliminatedCKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialEliminatedCKernel parameters L compact state) :=
  (radialNormalizedCKernel_regular parameters L compact state).comp (radialEliminatedSevenKernel_regular parameters L compact state)

theorem radialEliminatedRVKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialEliminatedRVKernel parameters L compact state) :=
  (radialNormalizedRVKernel_regular parameters L compact state).comp (radialEliminatedSevenKernel_regular parameters L compact state)

theorem radialEliminatedBulkKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialEliminatedBulkKernel parameters L compact state) :=
  (((constantMatrixRadialKernel_regular parameters _ _ _).comp (radialEliminatedXKernel_regular parameters L compact state)).add
    ((constantMatrixRadialKernel_regular parameters _ _ _).comp (radialEliminatedCKernel_regular parameters L compact state))).add
      ((constantMatrixRadialKernel_regular parameters _ _ _).comp (radialEliminatedRVKernel_regular parameters L compact state))

theorem radialEliminatedBulkError_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (fun r => fullKernelSub (radialEliminatedBulkKernel parameters L compact state r)
      (circularEliminatedBulkKernel (radialKernelParameters parameters r) L)) :=
  (radialEliminatedBulkKernel_regular parameters L compact state).sub
    (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L))

end Grad.AnnularReconstruction
