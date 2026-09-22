import AHV2FixedRetainedHighInverse

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

def radialNormalizedRetainedFirstRowKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
    (fullKernelSub
      (fullKernelComposition (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0)
        (radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property))
      (fullKernelComposition (radialRetainedForceKernel parameters L compact state.val r)
        (radialNormalizedCovariantKernel parameters L compact state.val r state.property)))

def circularRetainedFirstRowKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelSub
      (fullKernelComposition (coordinateProjectionKernel parameters 3 0)
        (circularNormalizedRotatedCovariantKernel parameters L))
      (fullKernelComposition (circularRetainedForceKernel parameters)
        (circularNormalizedCovariantKernel parameters L)))

def radialRetainedHighAKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state r)
    (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 7 0)
      (highAngularKernel (radialKernelParameters parameters r) 1))

def circularRetainedARecipe (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 1 1 :=
  fullKernelComposition (circularRetainedFirstRowKernel parameters L)
    (fullKernelComposition (coordinateInjectionKernel parameters 7 0) (highAngularKernel parameters 1))

theorem radialFixedHighMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : ℕ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => highAngularKernel (radialKernelParameters parameters r) dimension) :=
  RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)

theorem radialFixedProjectionMoments (parameters : PhaseParameters) (L compact : ℝ)
    (dimension : ℕ) (coordinate : Fin dimension) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => coordinateProjectionKernel (radialKernelParameters parameters r) dimension coordinate) :=
  RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedInjectionMoments (parameters : PhaseParameters) (L compact : ℝ)
    (dimension : ℕ) (coordinate : Fin dimension) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => coordinateInjectionKernel (radialKernelParameters parameters r) dimension coordinate) :=
  RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialNormalizedRetainedFirstRowKernel_referenceDifference
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (radialNormalizedRetainedFirstRowKernel parameters L compact)
      (fun _ r => circularRetainedFirstRowKernel (radialKernelParameters parameters r) L) := by
  apply RadialReferenceDifference.left (radialFixedHighMoments parameters L compact 1)
  exact (RadialReferenceDifference.left (radialFixedProjectionMoments parameters L compact 3 0)
    (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact)).sub
      ((radialRetainedForceKernel_referenceDifference parameters L compact).comp
        (radialNormalizedCovariantKernel_referenceDifference parameters L compact)
        (radialNormalizedCovariantKernel_physicalMoments parameters L compact)
        (circularRetainedForceKernel_physicalMoments parameters L compact))

theorem radialRetainedHighAKernel_recipeDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (radialRetainedHighAKernel parameters L compact)
      (fun _ r => circularRetainedARecipe (radialKernelParameters parameters r) L) := by
  exact (radialNormalizedRetainedFirstRowKernel_referenceDifference parameters L compact).right
    ((radialFixedInjectionMoments parameters L compact 7 0).comp (radialFixedHighMoments parameters L compact 1))

theorem radialRetainedHighAKernel_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialRetainedHighAKernel parameters L compact state r) = radialRetainedHighAKernel parameters L compact state r := by
  unfold radialRetainedHighAKernel radialNormalizedRetainedFirstRowKernel
  simp only [← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem radialRetainedHighAKernel_high_right (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighAKernel parameters L compact state r)
      (highAngularKernel (radialKernelParameters parameters r) 1) = radialRetainedHighAKernel parameters L compact state r := by
  unfold radialRetainedHighAKernel
  rw [fullKernelComposition_assoc, fullKernelComposition_assoc, highAngularKernel_idempotent]

end Grad.AnnularReconstruction
