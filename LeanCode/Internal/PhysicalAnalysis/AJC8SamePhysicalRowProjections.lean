import AJC7SameActualHighFluxAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.AnnularReconstruction
open Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularPhysicalSolution
open Grad.AnnularCurrentLow Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

theorem completedHighProjection_same (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    highBulkProjection parameters power lower positive bounded 1 = highRowProjection lower := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [highBulkProjection_ae parameters power lower positive bounded field,
    Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius actual zeroValue
  rw [actual mode]
  by_cases high : 3 ≤ |mode.1|
  · rw [highRowProjection_high lower field ⟨mode, high⟩]
    simp only [highAngularMultiplier, if_pos high, one_smul]
  · rw [highRowProjection_low lower field mode high, zeroValue]
    simp only [highAngularMultiplier, if_neg high, zero_smul, Pi.zero_apply]

/-- Q absorbs exactly the original mean-free projection P, on the output.
No projection is commuted through any variable coefficient. -/
theorem highAngularKernel_meanFree (parameters : PhaseParameters) (dimension : ℕ) :
    fullKernelComposition (highAngularKernel parameters dimension) (angularMeanFreeKernel parameters dimension) =
      highAngularKernel parameters dimension := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  unfold highAngularKernel angularMeanFreeKernel scalarModeDiagonalKernel
  rw [fullKernelComposition_entry, tsum_eq_single (0, 0) (by
    intro current nonzero
    rw [modeDiagonalKernel_entry, modeDiagonalKernel_entry]
    simp only [if_neg nonzero, ContinuousLinearMap.comp_zero])]
  rw [modeDiagonalKernel_entry, modeDiagonalKernel_entry, modeDiagonalKernel_entry]
  simp only [show shift - (0, 0) = shift from sub_zero shift, show frequency + (0, 0) = frequency from add_zero frequency]
  by_cases zero : shift = (0, 0)
  · rw [if_pos zero]
    apply ContinuousLinearMap.ext
    intro value
    simp only [ite_true, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      highAngularMultiplier_meanFree]
  · rw [if_neg zero]
    exact ContinuousLinearMap.zero_comp _

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

/-- The completed high c row is the high projection of the SAME full
physical c row used by the low equation. -/
theorem normalizedCBulkAction_sameFullRow :
    normalizedCBulkAction parameters L compact lower positive bounded state 0 =
      (highRowProjection lower).comp (lowPhysicalRowAction parameters L compact lower positive bounded state 1) := by
  have composed : normalizedCBulkAction parameters L compact lower positive bounded state 0 =
      (highBulkProjection parameters 0 lower positive bounded 1).comp
        (lowPhysicalRowAction parameters L compact lower positive bounded state 1) :=
    regularRadialBulkAction_comp parameters 0 lower positive bounded
      (fun radius => highAngularKernel (radialKernelParameters parameters radius) 1)
      (radialNormalizedUnprojectedCKernel parameters L compact state)
      (scalarModeRadialKernel_regular parameters 1 highAngularMultiplier 1 highAngularMultiplier_norm_le)
      (radialNormalizedUnprojectedCKernel_regular parameters L compact state)
  exact composed.trans (congrArg (fun projection : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower =>
    projection.comp (lowPhysicalRowAction parameters L compact lower positive bounded state 1))
      (completedHighProjection_same parameters 0 lower positive bounded))

theorem normalizedRVBulkAction_sameFullRow :
    normalizedRVBulkAction parameters L compact lower positive bounded state 0 =
      (highRowProjection lower).comp (lowPhysicalRowAction parameters L compact lower positive bounded state 2) := by
  let high := scalarModeRadialKernel_regular parameters 1 highAngularMultiplier 1 highAngularMultiplier_norm_le
  let physical := radialNormalizedPhysicalRVKernel_regular parameters L compact state
  have factor (radius : RadialPoint) :
      radialNormalizedRVKernel parameters L compact state radius =
        fullKernelComposition (highAngularKernel (radialKernelParameters parameters radius) 1)
          (radialNormalizedPhysicalRVKernel parameters L compact state radius) := by
    rw [radialNormalizedPhysicalRVKernel, ← fullKernelComposition_assoc, highAngularKernel_meanFree]
    rfl
  have same : normalizedRVBulkAction parameters L compact lower positive bounded state 0 =
      regularRadialBulkAction parameters 0 lower positive bounded
        (fun radius => fullKernelComposition (highAngularKernel (radialKernelParameters parameters radius) 1)
          (radialNormalizedPhysicalRVKernel parameters L compact state radius)) (high.comp physical) :=
    regularRadialBulkAction_congr parameters 0 lower positive bounded _ _ _ _ factor
  have composed : normalizedRVBulkAction parameters L compact lower positive bounded state 0 =
      (highBulkProjection parameters 0 lower positive bounded 1).comp
        (lowPhysicalRowAction parameters L compact lower positive bounded state 2) :=
    same.trans (regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ high physical)
  exact composed.trans (congrArg (fun projection : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower =>
    projection.comp (lowPhysicalRowAction parameters L compact lower positive bounded state 2))
      (completedHighProjection_same parameters 0 lower positive bounded))

end Grad.AnnularStrongSolution
