import AHV4CircularRetainedSymbol

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The original reciprocal-radius normalization fixes exactly the x slot. -/
theorem radialSevenSlotKernel_firstInjection (parameters : PhaseParameters) (r : RadialPoint) :
    fullKernelComposition (radialSevenSlotKernel parameters r)
      (coordinateInjectionKernel (radialKernelParameters parameters r) 7 0) =
      coordinateInjectionKernel (radialKernelParameters parameters r) 7 0 := by
  unfold radialSevenSlotKernel coordinateInjectionKernel
  rw [constantMatrixKernel_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [radialSevenSlotNormalization_apply, matrixUnit_apply, operatorBasis]

theorem radialRetainedFirstRowKernel_normalized (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) :
    radialRetainedFirstRowKernel parameters L compact state.val r state.property positive =
      fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state r)
        (radialSevenSlotKernel parameters r) := by
  unfold radialRetainedFirstRowKernel radialNormalizedRetainedFirstRowKernel
    radialRotatedCovariantKernel radialCovariantKernel
  simp only [fullKernelSub, fullKernelComposition_add_outer, fullKernelComposition_add_inner,
    fullKernelComposition_neg_outer, fullKernelComposition_neg_inner, fullKernelComposition_assoc]

/-- All-radius identification with the exact already extracted AHS A block,
restricted only to the prescribed high input. No width or source normalization changes. -/
theorem radialRetainedHighAKernel_original (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) :
    fullKernelComposition (radialRetainedAKernel parameters L compact state.val r state.property positive)
      (highAngularKernel (radialKernelParameters parameters r) 1) =
      radialRetainedHighAKernel parameters L compact state r := by
  unfold radialRetainedAKernel
  rw [radialRetainedFirstRowKernel_normalized,
    fullKernelComposition_assoc (radialNormalizedRetainedFirstRowKernel parameters L compact state r),
    radialSevenSlotKernel_firstInjection]
  exact fullKernelComposition_assoc _ _ _

theorem radialRetainedHighAKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact (radialRetainedHighAKernel parameters L compact)
      (fun _ r => circularRetainedAKernel (radialKernelParameters parameters r)) := by
  apply (radialRetainedHighAKernel_recipeDifference parameters L compact).congr (fun _ _ => rfl)
  intro state r
  exact circularRetainedARecipe_eq _ _

end Grad.AnnularReconstruction
