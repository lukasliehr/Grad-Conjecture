import AHW27ExactEliminatedPhysicalConsumer

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity

/-- Literal pre-Q rV includes AH23's P. The unprojected provider is its raw bracket. -/
def radialNormalizedPhysicalRVKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
    (radialNormalizedUnprojectedRVKernel parameters L compact state r)

def circularNormalizedPhysicalRVKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (angularMeanFreeKernel parameters 1) (circularNormalizedUnprojectedRVKernel parameters L)

theorem radialNormalizedPhysicalRVKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedReferenceDifference parameters L compact (radialNormalizedPhysicalRVKernel parameters L compact)
      (fun _ r => circularNormalizedPhysicalRVKernel (radialKernelParameters parameters r) L) :=
  RetainedReferenceDifference.left (retainedFixedMeanFreeMoments parameters L compact 1)
    (radialNormalizedUnprojectedRVKernel_referenceDifference parameters L compact)

theorem sameCircularNormalizedPhysicalRVKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedPhysicalRVKernel first L) (circularNormalizedPhysicalRVKernel second L) :=
  (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp (sameCircularNormalizedUnprojectedRVKernel first second L)

theorem radialNormalizedPhysicalRVKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RetainedPhysicalMoments parameters L compact (radialNormalizedPhysicalRVKernel parameters L compact) :=
  (radialNormalizedPhysicalRVKernel_referenceDifference parameters L compact).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularNormalizedPhysicalRVKernel _ _ L))

theorem radialNormalizedPhysicalRVKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialNormalizedPhysicalRVKernel parameters L compact state) :=
  (scalarModeRadialKernel_regular parameters _ _ _ _).comp
    (radialNormalizedUnprojectedRVKernel_regular parameters L compact state)

theorem circularNormalizedPhysicalRVKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularNormalizedPhysicalRVKernel parameters L) := by
  unfold circularNormalizedPhysicalRVKernel angularMeanFreeKernel scalarModeDiagonalKernel
  exact (zeroShift_modeDiagonal _ _ _ _ _ _).comp (circularNormalizedUnprojectedRVKernel_zeroShift parameters L)

/-- The physical circular pre-Q rV kills the mean term by P itself. -/
theorem circularNormalizedPhysicalRVKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 7) :
    (circularNormalizedPhysicalRVKernel parameters L).entry (0, 0) mode value 0 =
      angularMeanFreeMultiplier mode * (-value 1 - 2 * angularInverseMultiplier mode * value 0) := by
  rw [circularNormalizedPhysicalRVKernel,
    kernelComposition_entry_diagonal_inner _ _ (circularNormalizedUnprojectedRVKernel_zeroShift parameters L)]
  change angularMeanFreeMultiplier mode *
    ((circularNormalizedUnprojectedRVKernel parameters L).entry (0, 0) mode value) 0 = _
  rw [circularNormalizedUnprojectedRVKernel_entry_zero]
  by_cases zero : mode.1 = 0 <;> simp [angularMeanFreeMultiplier, angularMeanMultiplier, zero]

/-- Exact high consumer absorbs only the prescribed P, without a commutation through cofactor multiplication. -/
theorem radialNormalizedPhysicalRVKernel_high_action (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 7) :
    fullNegativeKernelAction _ angular cell (highAngularKernel (radialKernelParameters parameters r) 1)
      (fullNegativeKernelAction _ angular cell (radialNormalizedPhysicalRVKernel parameters L compact state r) input) =
    fullNegativeKernelAction _ angular cell (radialNormalizedRVKernel parameters L compact state r) input := by
  simp only [radialNormalizedPhysicalRVKernel, radialNormalizedRVKernel_projected, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, highAngular_action_meanFree_eq]

theorem radialNormalizedPhysicalRVKernel_originalPhysical (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction _ angular cell (radialNormalizedPhysicalRVKernel parameters L compact state r)
      (sevenSlotFlatten _ angular cell (radialNormalizedSevenInput parameters r angular cell input)) =
    (r.val : ℂ) • (originalPhysicalVTrace parameters L compact state r angular cell
        (fullNegativeKernelAction _ angular cell
          (radialCovariantKernel parameters L compact state.val.val r state.val.property positive)
          (sevenSlotFlatten _ angular cell input)) (input 3) (input 1)) := by
  have nonzero : (r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [radialNormalizedPhysicalRVKernel, radialNormalizedUnprojectedRVKernel,
    fullNegativeKernelAction_comp, fullNegativeKernelAction_sub, fullNegativeKernelAction_add,
    fullNegativeKernelAction_smul, ContinuousLinearMap.comp_apply, 
    sevenInputSlotKernel_flatten,
    originalPhysicalVTrace,
    radialCovariantKernel, radialSevenSlotKernel_action]
  simp only [radialNormalizedSevenInput, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, map_smul, map_add, map_sub, smul_add, smul_sub, smul_smul]
  simp only [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
  have axial : (r.val : ℂ) * (L : ℂ)⁻¹ * (r.val : ℂ)⁻¹ = (L : ℂ)⁻¹ := by
    rw [mul_right_comm, mul_inv_cancel₀ nonzero, one_mul]
  rw [axial]
  module

end Grad.AnnularReconstruction
