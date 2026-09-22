import BCI7BoundaryBaseSmallness

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

 theorem fullKernel_neg_zero (parameters : PhaseParameters) (input output : ℕ) :
    fullKernelNeg (fullZeroKernel parameters input output) = fullZeroKernel parameters input output := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelNeg_entry]

theorem fullKernel_comp_identity_rect {input output : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters input output) :
    fullKernelComposition kernel (fullIdentityKernel parameters input) = kernel := by
  rw [← constantMatrixKernel_id]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [constantKernel_inner_entry]
  exact ContinuousLinearMap.comp_id _

theorem known_reconstruction_x {parameters : PhaseParameters} {output : ℕ}
    (unknown : FullTwoFrequencyKernel parameters 1 output)
    (inverse : FullTwoFrequencyKernel parameters 1 1)
    (known : FullTwoFrequencyKernel parameters 7 output) (knownJ : FullTwoFrequencyKernel parameters 7 1)
    (knownIgnored : IgnoresFirstSlot known) (jIgnored : IgnoresFirstSlot knownJ) :
    fullKernelComposition
      (fullKernelAdd (fullKernelComposition unknown (fullKernelComposition inverse
        (fullKernelSub (sevenInputSlotKernel parameters 0) knownJ))) known)
      (coordinateInjectionKernel parameters 7 0) = fullKernelComposition unknown inverse := by
  unfold IgnoresFirstSlot at knownIgnored jIgnored
  rw [fullKernelComposition_add_outer, fullKernelComposition_assoc, fullKernelComposition_assoc,
    fullKernelSub, fullKernelComposition_add_outer, fullKernelComposition_neg_outer,
    sevenInputSlotKernel, coordinateProjection_injection_same, jIgnored, fullKernel_neg_zero,
    fullKernel_add_zero, fullKernel_comp_identity, knownIgnored, fullKernel_add_zero]

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem actual_covariant_x (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition state.covariant (coordinateInjectionKernel parameters 7 0) =
      fullKernelComposition state.unknownU state.massInverse := by
  exact known_reconstruction_x state.unknownU state.massInverse state.knownA state.knownJ
    (actualKnownAStarKernel_ignores parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
      state.val.deltaSmall state.val.parameterSmall)
    (actualKnownJStarKernel_ignores parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
      state.val.deltaSmall state.val.parameterSmall)

theorem actual_rotated_covariant_x (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition state.rotatedCovariant (coordinateInjectionKernel parameters 7 0) =
      fullKernelComposition state.unknownV state.massInverse := by
  exact known_reconstruction_x state.unknownV state.massInverse state.knownRA state.knownJ
    (actualKnownRAStarKernel_ignores parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
      state.val.deltaSmall state.val.parameterSmall)
    (actualKnownJStarKernel_ignores parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
      state.val.deltaSmall state.val.parameterSmall)

/-- The exact AF mass inverse supplies its reference difference algebraically. -/
theorem massInverse_reference_difference (state : PhysicalBoundaryState parameters L compact) :
    fullKernelAdd state.massInverse (fullIdentityKernel parameters 1) =
      fullKernelComposition state.massPerturbation state.massInverse := by
  have inverse := actualMassInverseKernel_right parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
  change fullKernelComposition (fullKernelNegativeIdentityPerturbation parameters state.massPerturbation) state.massInverse = _ at inverse
  rw [fullKernelNegativeIdentityPerturbation, fullKernelSub, fullKernelComposition_add_outer,
    fullKernelComposition_neg_outer, fullIdentityKernel_comp] at inverse
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have entry := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 => kernel.entry shift frequency) inverse
  simp only [fullKernelAdd_entry, fullKernelNeg_entry] at entry ⊢
  exact (add_comm _ _).trans (eq_add_of_sub_eq (show _ - _ = _ from entry)).symm

end Grad.ActualBoundaryInverse
