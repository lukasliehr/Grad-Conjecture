import BCI15FullBoundaryReferenceDeviation

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem highBoundaryInverse_reference_tail (state : BoundaryInverseState parameters L compact) :
    fullKernelAdd (actualHighBoundaryInverse state.val state.property) (highAngularKernel parameters 1) =
      fullKernelNeg (fullKernelComposition (highAngularKernel parameters 1)
        (fullKernelNeumannTail parameters state.val.boundaryE (1 / 4)
          (boundary_E_le_quarter state.val state.property) (by norm_num))) := by
  unfold actualHighBoundaryInverse actualBoundaryAmbientInverse fullKernelNegativeIdentityInverse fullKernelNeumannSum
  rw [fullKernelComposition_neg_inner, fullKernelComposition_add_inner, fullKernel_comp_identity]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp only [fullKernelAdd_entry, fullKernelNeg_entry]
  abel

/-- AI10's sharp inverse-reference moment estimate on the original single
low ball. The reference contribution is Q, since the inverse is -I_Q. -/
theorem actualHighBoundaryInverse_referenceMoments (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : BoundaryInverseState parameters L compact,
      fullKernelMoment parameters moment
        (fullKernelAdd (actualHighBoundaryInverse state.val state.property) (highAngularKernel parameters 1)) ≤
        constant * state.val.budget moment := by
  obtain ⟨highConstant, highNonnegative, highBound⟩ := actualBoundaryE_vanishingMoments parameters L compact moment
  obtain ⟨baseConstant, baseNonnegative, baseBound⟩ := actualBoundaryE_vanishingMoments parameters L compact 0
  have neumannNonnegative (q : ℕ) : 0 ≤ fullKernelNeumannConstant q (1 / 4) := by
    unfold fullKernelNeumannConstant
    exact tsum_nonneg (fun _ => by positivity)
  let constant := 2 ^ moment *
    (fullKernelMoment parameters moment (highAngularKernel parameters 1) * fullKernelNeumannConstant 0 (1 / 4) * baseConstant +
      fullKernelMoment parameters 0 (highAngularKernel parameters 1) * fullKernelNeumannConstant moment (1 / 4) * highConstant)
  refine ⟨constant, mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg (mul_nonneg (fullKernelMoment_nonnegative parameters moment _) (neumannNonnegative 0)) baseNonnegative)
    (mul_nonneg (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _) (neumannNonnegative moment)) highNonnegative)), ?_⟩
  intro state
  let tail := fullKernelNeumannTail parameters state.val.boundaryE (1 / 4)
    (boundary_E_le_quarter state.val state.property) (by norm_num)
  have tailHigh : fullKernelMoment parameters moment tail ≤
      fullKernelNeumannConstant moment (1 / 4) * highConstant * state.val.budget moment := by
    apply (fullKernelNeumannTail_moment_le parameters moment state.val.boundaryE (1 / 4)
      (boundary_E_le_quarter state.val state.property) (by norm_num)).trans
    exact (mul_le_mul_of_nonneg_left (highBound state.val) (neumannNonnegative moment)).trans_eq (mul_assoc _ _ _).symm
  have tailBase : fullKernelMoment parameters 0 tail ≤
      fullKernelNeumannConstant 0 (1 / 4) * baseConstant * state.val.budget moment := by
    apply (fullKernelNeumannTail_moment_le parameters 0 state.val.boundaryE (1 / 4)
      (boundary_E_le_quarter state.val state.property) (by norm_num)).trans
    have budget : state.val.budget 0 ≤ state.val.budget moment :=
      physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)
    have bound := (baseBound state.val).trans (mul_le_mul_of_nonneg_left budget baseNonnegative)
    exact (mul_le_mul_of_nonneg_left bound (neumannNonnegative 0)).trans_eq (mul_assoc _ _ _).symm
  rw [highBoundaryInverse_reference_tail]
  apply (fullKernelNeg_moment_le parameters moment _).trans
  apply (fullKernelComposition_moment_le moment (highAngularKernel parameters 1) tail).trans
  have first := mul_le_mul_of_nonneg_left tailBase (fullKernelMoment_nonnegative parameters moment (highAngularKernel parameters 1))
  have second := mul_le_mul_of_nonneg_left tailHigh (fullKernelMoment_nonnegative parameters 0 (highAngularKernel parameters 1))
  exact (mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by dsimp [constant]; ring)

end Grad.ActualBoundaryInverse
