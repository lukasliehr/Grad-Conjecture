import AHW16UnprojectedPhysicalFluxErrors

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity

def radialNormalizedUnprojectedFirstRowKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelSub
    (fullKernelComposition (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)
      (radialNormalizedRotatedCovariantKernel parameters L compact state.val.val r state.val.property))
    (fullKernelComposition (radialRetainedForceKernel parameters L compact state.val.val r)
      (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property))

def circularNormalizedUnprojectedFirstRowKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelSub
    (fullKernelComposition (coordinateProjectionKernel parameters 3 0) (circularNormalizedRotatedCovariantKernel parameters L))
    (fullKernelComposition (circularRetainedForceKernel parameters) (circularNormalizedCovariantKernel parameters L))

theorem radialNormalizedRetainedFirstRowKernel_projected (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    radialNormalizedRetainedFirstRowKernel parameters L compact state.val r =
      fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (radialNormalizedUnprojectedFirstRowKernel parameters L compact state r) := rfl

theorem radialNormalizedUnprojectedFirstRowKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedUnprojectedFirstRowKernel parameters L compact)
      (fun _ r => circularNormalizedUnprojectedFirstRowKernel (radialKernelParameters parameters r) L) := by
  have force : RetainedReferenceDifference parameters L compact
      (fun state r => radialRetainedForceKernel parameters L compact state.val.val r)
      (fun _ r => circularRetainedForceKernel (radialKernelParameters parameters r)) :=
    RetainedDeviationMoments.restrict (radialRetainedForceKernel_referenceDifference parameters L compact)
  exact (RetainedReferenceDifference.left
    (RetainedPhysicalMoments.restrict (radialFixedProjectionMoments parameters L compact 3 0))
    (retainedNormalizedRotatedDifference parameters L compact)).sub
      (force.comp (retainedNormalizedCovariantDifference parameters L compact)
        (retainedNormalizedCovariantMoments parameters L compact)
        (RetainedPhysicalMoments.restrict (circularRetainedForceKernel_physicalMoments parameters L compact)))

theorem sameCircularNormalizedUnprojectedFirstRowKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedUnprojectedFirstRowKernel first L) (circularNormalizedUnprojectedFirstRowKernel second L) :=
  ((sameConstantMatrixKernel _ _ _ _ _).comp (sameCircularNormalizedRotatedCovariantKernel first second L)).sub
    (((sameConstantMatrixKernel _ _ _ _ _).smul 2).comp (sameCircularNormalizedCovariantKernel first second L))

theorem radialNormalizedUnprojectedFirstRowKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedUnprojectedFirstRowKernel parameters L compact) :=
  (radialNormalizedUnprojectedFirstRowKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedUnprojectedFirstRowKernel _ _ L))

theorem radialNormalizedUnprojectedFirstRowKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialNormalizedUnprojectedFirstRowKernel parameters L compact state) :=
  ((constantMatrixRadialKernel_regular parameters _ _ _).comp
    (radialNormalizedRotatedCovariantKernel_regular parameters L compact state.val)).sub
      ((radialRetainedForceKernel_regular parameters L compact state.val).comp
        (radialNormalizedCovariantKernel_regular parameters L compact state.val))

theorem radialOriginalForceZeroKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialOriginalForceZeroKernel parameters L compact state) :=
  (fixedRadialKernel_regular parameters _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul (-2))).add
    (radialForceKernel_regular parameters L compact state.val.val 0 0)

theorem radialKVKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : RegularKernelFamily (radialKVKernel parameters L compact state) := by
  unfold radialKVKernel
  with_reducible repeat' first
    | exact radialCofactorJetRowKernel_regular parameters L compact state 1 0 1
    | exact radialSignedCofactorComponentKernel_regular parameters L compact state 1 0
    | exact radialSignedCofactorComponentKernel_regular parameters L compact state 1 1
    | exact radialSignedCofactorComponentKernel_regular parameters L compact state 1 2
    | exact radialRetainedForceKernel_regular parameters L compact state.val
    | exact radialOriginalForceZeroKernel_regular parameters L compact state
    | exact radialForceKernel_regular parameters L compact state.val.val 1 0
    | apply RegularKernelFamily.comp
    | apply RegularKernelFamily.add
    | apply RegularKernelFamily.sub
  all_goals exact scalarModeRadialKernel_regular parameters _ _ _ _

theorem radialNormalizedUnprojectedCKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialNormalizedUnprojectedCKernel parameters L compact state) := by
  unfold radialNormalizedUnprojectedCKernel
  with_reducible repeat' first
    | exact radialCofactorJetRowKernel_regular parameters L compact state 2 0 1
    | exact radialSignedCofactorRowKernel_regular parameters L compact state 2
    | exact radialCofactorJetComponentKernel_regular parameters L compact state 1 2 0 1
    | exact radialSignedCofactorComponentKernel_regular parameters L compact state 1 2
    | exact radialNormalizedCovariantKernel_regular parameters L compact state.val
    | exact radialNormalizedRotatedCovariantKernel_regular parameters L compact state.val
    | apply RegularKernelFamily.comp
    | apply RegularKernelFamily.add
  all_goals exact constantMatrixRadialKernel_regular parameters _ _ _

theorem radialNormalizedUnprojectedRVKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialNormalizedUnprojectedRVKernel parameters L compact state) := by
  have slotRegular : RegularKernelFamily (fun r => sevenInputSlotKernel (radialKernelParameters parameters r) 3) :=
    constantMatrixRadialKernel_regular parameters _ _ _
  have radialTerm := RegularKernelFamily.radial_smul
    ((radialCofactorJetComponentKernel_regular parameters L compact state 1 0 1 0).comp slotRegular) (fun r => (r.val : ℂ))
      (Complex.continuous_ofReal.comp continuous_subtype_val) 1 (by norm_num) radialPoint_norm_le_one
  have axialTerm := RegularKernelFamily.radial_smul
    ((radialCofactorJetComponentKernel_regular parameters L compact state 1 2 0 2).comp slotRegular) (fun r => (r.val : ℂ) * (L : ℂ)⁻¹)
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const) ‖(L : ℂ)⁻¹‖ (norm_nonneg _) (fun r => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (radialPoint_norm_le_one r) (norm_nonneg _)).trans_eq (one_mul _))
  exact ((((radialSignedCofactorComponentKernel_regular parameters L compact state 1 1).comp
    (constantMatrixRadialKernel_regular parameters _ _ _)).add
      ((radialKVKernel_regular parameters L compact state).comp
        (radialNormalizedCovariantKernel_regular parameters L compact state.val))).sub radialTerm).sub axialTerm

end Grad.AnnularReconstruction
