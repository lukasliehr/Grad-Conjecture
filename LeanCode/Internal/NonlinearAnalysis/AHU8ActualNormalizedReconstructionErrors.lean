import AHU7ActualScalarMassErrors

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Exact circular reconstruction on the same seven normalized ambient inputs. -/
def circularNormalizedCovariantKernel (parameters : PhaseParameters) (L : ℝ) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd
    (fullKernelComposition (circularUnknownUKernel parameters) (circularRecoveredMassKernel parameters))
    (circularKnownAStarKernel parameters L)

def circularNormalizedRotatedCovariantKernel (parameters : PhaseParameters) (L : ℝ) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd
    (fullKernelComposition (circularUnknownVKernel parameters) (circularRecoveredMassKernel parameters))
    (circularKnownRAStarKernel parameters L)

/-- The error comes from the actual coefficient constructions and ordered resolvents;
no generic error matrix or comparison hypothesis is supplied. -/
theorem radialNormalizedCovariantKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialNormalizedCovariantKernel parameters L compact state.val r state.property)
      (fun _ r => circularNormalizedCovariantKernel (radialKernelParameters parameters r) L) := by
  exact ((radialUnknownUKernel_referenceDifference parameters L compact).comp
    (radialRecoveredMassKernel_referenceDifference parameters L compact)
    (radialRecoveredMassKernel_physicalMoments parameters L compact)
    (circularUnknownUKernel_physicalMoments parameters L compact)).add
      (radialKnownAStarKernel_referenceDifference parameters L compact)

theorem radialNormalizedRotatedCovariantKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property)
      (fun _ r => circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters r) L) := by
  exact ((radialUnknownVKernel_referenceDifference parameters L compact).comp
    (radialRecoveredMassKernel_referenceDifference parameters L compact)
    (radialRecoveredMassKernel_physicalMoments parameters L compact)
    (circularUnknownVKernel_physicalMoments parameters L compact)).add
      (radialKnownRAStarKernel_referenceDifference parameters L compact)

/-- A shared constant controls both actual errors at every radius and grade.
In particular grade 1 is linear in the original physical B8 budget. -/
theorem actualRadialNormalizedReconstruction_error_moments
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint),
        fullKernelMoment (radialKernelParameters parameters r) moment
          (fullKernelSub
            (radialNormalizedCovariantKernel parameters L compact state.val r state.property)
            (circularNormalizedCovariantKernel (radialKernelParameters parameters r) L)) ≤
          constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 7) ∧
        fullKernelMoment (radialKernelParameters parameters r) moment
          (fullKernelSub
            (radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property)
            (circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters r) L)) ≤
          constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 7) := by
  obtain ⟨first, firstNonnegative, firstBound⟩ :=
    radialNormalizedCovariantKernel_referenceDifference parameters L compact moment
  obtain ⟨second, secondNonnegative, secondBound⟩ :=
    radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact moment
  refine ⟨max first second, le_max_of_le_left firstNonnegative, ?_⟩
  intro state r
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7)
  constructor
  · exact (firstBound state r).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) budgetNonnegative)
  · exact (secondBound state r).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) budgetNonnegative)

end Grad.AnnularReconstruction
