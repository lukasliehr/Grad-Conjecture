import AHV5OriginalRetainedAIdentification

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

def radialRetainedHighErrorKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelSub (radialRetainedHighAKernel parameters L compact state r)
    (circularRetainedAKernel (radialKernelParameters parameters r))

def radialRetainedPreconditionKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelComposition (retainedBInverseKernel (radialKernelParameters parameters r))
    (radialRetainedHighErrorKernel parameters L compact state r)

theorem radialRetainedPreconditionKernel_vanishingMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact (radialRetainedPreconditionKernel parameters L compact) :=
  RadialDeviationMoments.regular_comp (retainedBInverseKernel_physicalMoments parameters L compact)
    (radialRetainedHighAKernel_referenceDifference parameters L compact)

def retainedInverseBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  Classical.choose (radialRetainedPreconditionKernel_vanishingMoments parameters L compact 0)

theorem retainedInverseBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ retainedInverseBaseConstant parameters L compact :=
  (Classical.choose_spec (radialRetainedPreconditionKernel_vanishingMoments parameters L compact 0)).1

/-- One B7 ball precedes all radii and grades, also fitting the frozen outer inverse. -/
def retainedInverseLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (boundaryInverseLowRadius parameters L compact)
    (2 * (retainedInverseBaseConstant parameters L compact + 1))⁻¹

theorem retainedInverseLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < retainedInverseLowRadius parameters L compact := by
  apply lt_min (boundaryInverseLowRadius_positive parameters L compact)
  apply inv_pos.mpr
  have := retainedInverseBaseConstant_nonnegative parameters L compact
  linarith

abbrev RetainedInverseState (parameters : PhaseParameters) (L compact : ℝ) :=
  {state : AnnularReconstructionState parameters L compact //
    state.errorBudget 0 ≤ retainedInverseLowRadius parameters L compact}

namespace RetainedInverseState
variable {parameters : PhaseParameters} {L compact : ℝ}

def boundaryState (state : RetainedInverseState parameters L compact) : PhysicalBoundaryState parameters L compact :=
  ⟨state.val.val, (state.property.trans (min_le_left _ _)).trans (min_le_left _ _)⟩

def outerInverseState (state : RetainedInverseState parameters L compact) : BoundaryInverseState parameters L compact :=
  ⟨state.boundaryState, state.property.trans (min_le_left _ _)⟩
end RetainedInverseState

theorem radialRetainedPreconditionKernel_small (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialRetainedPreconditionKernel parameters L compact state.val r) ≤ 1 / 2 := by
  have bound := (Classical.choose_spec
    (radialRetainedPreconditionKernel_vanishingMoments parameters L compact 0)).2 state.val r
  have small := state.property.trans (min_le_right _ _)
  have nonnegative := retainedInverseBaseConstant_nonnegative parameters L compact
  change _ ≤ retainedInverseBaseConstant parameters L compact * state.val.errorBudget 0 at bound
  apply (bound.trans (mul_le_mul_of_nonneg_left small nonnegative)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 2 * (retainedInverseBaseConstant parameters L compact + 1))).2
  linarith

def radialRetainedAmbientInverse (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelNegativeIdentityInverse (radialKernelParameters parameters r)
    (radialRetainedPreconditionKernel parameters L compact state.val r) (1 / 2)
    (radialRetainedPreconditionKernel_small parameters L compact state r) (by norm_num)

/-- The actual inverse uses the existing convergent Neumann construction and
fixed b_m inverse. Its reference is -b_m inverse on the high sector. -/
def radialRetainedHighInverse (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelComposition (radialRetainedAmbientInverse parameters L compact state r)
    (retainedBInverseKernel (radialKernelParameters parameters r))

theorem radialRetainedAmbientInverse_right (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition
      (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialRetainedPreconditionKernel parameters L compact state.val r))
      (radialRetainedAmbientInverse parameters L compact state r) =
      fullIdentityKernel (radialKernelParameters parameters r) 1 :=
  fullKernelNegativeIdentity_inverse_right _ _ _ _ _

theorem radialRetainedAmbientInverse_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedAmbientInverse parameters L compact state r)
      (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialRetainedPreconditionKernel parameters L compact state.val r)) =
      fullIdentityKernel (radialKernelParameters parameters r) 1 :=
  fullKernelNegativeIdentity_inverse_left _ _ _ _ _

end Grad.AnnularReconstruction
