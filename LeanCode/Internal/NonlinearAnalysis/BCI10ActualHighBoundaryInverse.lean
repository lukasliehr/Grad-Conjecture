import BCI9ExactHighBoundaryError

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem boundary_E_high_left (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) state.boundaryE = state.boundaryE := by
  unfold PhysicalBoundaryState.boundaryE
  rw [← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem boundary_E_high_right (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition state.boundaryE (highAngularKernel parameters 1) = state.boundaryE := by
  unfold PhysicalBoundaryState.boundaryE
  rw [fullKernelComposition_assoc, fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem boundaryT_eq_negativeIdentity_high (state : PhysicalBoundaryState parameters L compact) :
    state.boundaryT = fullKernelComposition
      (fullKernelNegativeIdentityPerturbation parameters state.boundaryE) (highAngularKernel parameters 1) := by
  rw [fullKernelNegativeIdentityPerturbation, fullKernelSub, fullKernelComposition_add_outer,
    boundary_E_high_right, fullKernelComposition_neg_outer, fullIdentityKernel_comp]
  have identity := boundaryT_add_high_eq_error state
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have entries := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 => kernel.entry shift frequency) identity
  simp only [fullKernelAdd_entry, fullKernelNeg_entry] at entries ⊢
  exact eq_sub_of_add_eq entries

theorem boundaryT_eq_high_negativeIdentity (state : PhysicalBoundaryState parameters L compact) :
    state.boundaryT = fullKernelComposition (highAngularKernel parameters 1)
      (fullKernelNegativeIdentityPerturbation parameters state.boundaryE) := by
  rw [fullKernelNegativeIdentityPerturbation, fullKernelSub, fullKernelComposition_add_inner,
    boundary_E_high_left, fullKernelComposition_neg_inner, fullKernel_comp_identity]
  have identity := boundaryT_add_high_eq_error state
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have entries := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 => kernel.entry shift frequency) identity
  simp only [fullKernelAdd_entry, fullKernelNeg_entry] at entries ⊢
  exact eq_sub_of_add_eq entries

/-- AI10: the actual convergent Neumann inverse on the complete ambient trace,
extended by -I on the complementary angular sector. -/
def actualBoundaryAmbientInverse (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 1 1 :=
  fullKernelNegativeIdentityInverse parameters state.boundaryE (1 / 4) (boundary_E_le_quarter state small) (by norm_num)

/-- Restriction of the actual Neumann inverse to the fixed high angular sector. -/
def actualHighBoundaryInverse (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 1 1 :=
  fullKernelComposition (highAngularKernel parameters 1) (actualBoundaryAmbientInverse state small)

theorem actualBoundaryAmbientInverse_right (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition (fullKernelNegativeIdentityPerturbation parameters state.boundaryE)
      (actualBoundaryAmbientInverse state small) = fullIdentityKernel parameters 1 :=
  fullKernelNegativeIdentity_inverse_right parameters state.boundaryE (1 / 4) (boundary_E_le_quarter state small) (by norm_num)

theorem actualBoundaryAmbientInverse_left (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition (actualBoundaryAmbientInverse state small)
      (fullKernelNegativeIdentityPerturbation parameters state.boundaryE) = fullIdentityKernel parameters 1 :=
  fullKernelNegativeIdentity_inverse_left parameters state.boundaryE (1 / 4) (boundary_E_le_quarter state small) (by norm_num)

theorem boundaryT_high_right (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition state.boundaryT (highAngularKernel parameters 1) = state.boundaryT := by
  rw [boundaryT_eq_negativeIdentity_high, fullKernelComposition_assoc, highAngularKernel_idempotent]

/-- First of the two actual AI10 inverse identities, with unit I_Q. -/
theorem actualHighBoundaryInverse_right (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition state.boundaryT (actualHighBoundaryInverse state small) = highAngularKernel parameters 1 := by
  unfold actualHighBoundaryInverse
  rw [← fullKernelComposition_assoc, boundaryT_high_right, boundaryT_eq_high_negativeIdentity,
    fullKernelComposition_assoc, actualBoundaryAmbientInverse_right, fullKernel_comp_identity]

/-- The opposite identity holds on the same B7 ball at every moment. -/
theorem actualHighBoundaryInverse_left (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition (actualHighBoundaryInverse state small) state.boundaryT = highAngularKernel parameters 1 := by
  unfold actualHighBoundaryInverse
  rw [boundaryT_eq_negativeIdentity_high, fullKernelComposition_assoc,
    ← fullKernelComposition_assoc (actualBoundaryAmbientInverse state small), actualBoundaryAmbientInverse_left,
    fullIdentityKernel_comp, highAngularKernel_idempotent]

theorem actualHighBoundaryInverse_high_left (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) (actualHighBoundaryInverse state small) =
      actualHighBoundaryInverse state small := by
  unfold actualHighBoundaryInverse
  rw [← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem actualHighBoundaryInverse_high_right (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelComposition (actualHighBoundaryInverse state small) (highAngularKernel parameters 1) =
      actualHighBoundaryInverse state small := by
  rw [← actualHighBoundaryInverse_right state small, ← fullKernelComposition_assoc,
    actualHighBoundaryInverse_left, actualHighBoundaryInverse_high_left]

end Grad.ActualBoundaryInverse
