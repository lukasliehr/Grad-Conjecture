import BCI8BoundaryReferenceAlgebra

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

 theorem highAngularKernel_idempotent (parameters : PhaseParameters) (dimension : ℕ) :
    fullKernelComposition (highAngularKernel parameters dimension) (highAngularKernel parameters dimension) =
      highAngularKernel parameters dimension := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  unfold highAngularKernel scalarModeDiagonalKernel
  rw [fullKernelComposition_entry, tsum_eq_single (0, 0) (by
    intro current nonzero
    rw [modeDiagonalKernel_entry, modeDiagonalKernel_entry]
    simp only [if_neg nonzero, ContinuousLinearMap.comp_zero])]
  rw [modeDiagonalKernel_entry, modeDiagonalKernel_entry, modeDiagonalKernel_entry]
  simp only [show shift - (0, 0) = shift from sub_zero shift, show frequency + (0, 0) = frequency from add_zero frequency]
  by_cases zero : shift = (0, 0)
  · rw [if_pos zero]
    have zeroId : (0 : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension) = 0 :=
      zero_smul ℂ (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))
    unfold highAngularMultiplier
    split_ifs <;> simp [zeroId]
  · rw [if_neg zero]
    exact ContinuousLinearMap.zero_comp _

variable {parameters : PhaseParameters} {L compact : ℝ}

 theorem physical_row_x_reference (state : PhysicalBoundaryState parameters L compact) :
    state.boundaryT = fullKernelComposition (highAngularKernel parameters 1)
      (fullKernelComposition
        (fullKernelComposition (fullKernelAdd state.rowCorrection (fullIdentityKernel parameters 1)) state.massInverse)
        (highAngularKernel parameters 1)) := by
  let lambda := actualBoundaryMultiplier parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
  let rotatedLambda := actualRotatedBoundaryMultiplier parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
  have lambdaLaw : lambda = fullKernelAdd state.deltaRow (coordinateProjectionKernel parameters 3 0) :=
    actualBoundaryMultiplier_decomposition parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
      state.val.parameterSmall state.coefficientSmall
  have rotatedLaw : rotatedLambda = state.rotatedDeltaRow :=
    actualRotatedBoundaryMultiplier_decomposition parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
      state.val.parameterSmall state.coefficientSmall
  have firstV : fullKernelComposition (coordinateProjectionKernel parameters 3 0) state.unknownV = fullIdentityKernel parameters 1 :=
    actualUnknownVKernel_first_kernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
      state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
      state.val.deltaSmall state.val.parameterSmall
  have raw : fullKernelComposition
      (fullKernelAdd (fullKernelComposition rotatedLambda state.covariant)
        (fullKernelComposition lambda state.rotatedCovariant))
      (coordinateInjectionKernel parameters 7 0) =
      fullKernelComposition (fullKernelAdd state.rowCorrection (fullIdentityKernel parameters 1)) state.massInverse := by
    rw [fullKernelComposition_add_outer]
    simp only [fullKernelComposition_assoc, actual_covariant_x, actual_rotated_covariant_x]
    rw [← fullKernelComposition_assoc, ← fullKernelComposition_assoc, lambdaLaw, rotatedLaw,
      fullKernelComposition_add_outer state.deltaRow (coordinateProjectionKernel parameters 3 0) state.unknownV,
      firstV, ← fullKernelComposition_add_outer]
    apply congrArg (fun outer : FullTwoFrequencyKernel parameters 1 1 => fullKernelComposition outer state.massInverse)
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    simp only [PhysicalBoundaryState.rowCorrection, fullKernelAdd_entry]
    exact (add_assoc _ _ _).symm
  change fullKernelComposition
    (fullKernelComposition (highAngularKernel parameters 1)
      (fullKernelAdd (fullKernelComposition rotatedLambda state.covariant)
        (fullKernelComposition lambda state.rotatedCovariant)))
    (fullKernelComposition (coordinateInjectionKernel parameters 7 0) (highAngularKernel parameters 1)) = _
  rw [fullKernelComposition_assoc, ← fullKernelComposition_assoc _ _ (highAngularKernel parameters 1), raw]

/-- Exact AI9: T=-I on Q plus the ordered vanishing perturbation. -/
theorem boundaryT_add_high_eq_error (state : PhysicalBoundaryState parameters L compact) :
    fullKernelAdd state.boundaryT (highAngularKernel parameters 1) = state.boundaryE := by
  have middle : fullKernelAdd
      (fullKernelComposition (fullKernelAdd state.rowCorrection (fullIdentityKernel parameters 1)) state.massInverse)
      (fullIdentityKernel parameters 1) =
      fullKernelComposition (fullKernelAdd state.massPerturbation state.rowCorrection) state.massInverse := by
    rw [fullKernelComposition_add_outer, fullIdentityKernel_comp, fullKernelComposition_add_outer]
    have mass := massInverse_reference_difference state
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    have massEntry := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 => kernel.entry shift frequency) mass
    simp only [fullKernelAdd_entry] at massEntry ⊢
    rw [add_assoc, massEntry, add_comm]
  rw [physical_row_x_reference]
  change fullKernelAdd (fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelComposition _ (highAngularKernel parameters 1))) (highAngularKernel parameters 1) = _
  have high : highAngularKernel parameters 1 = fullKernelComposition (highAngularKernel parameters 1)
      (fullKernelComposition (fullIdentityKernel parameters 1) (highAngularKernel parameters 1)) := by
    rw [fullIdentityKernel_comp, highAngularKernel_idempotent]
  conv_lhs => rhs; rw [high]
  rw [← fullKernelComposition_add_inner, ← fullKernelComposition_add_outer, middle]
  rfl

end Grad.ActualBoundaryInverse
