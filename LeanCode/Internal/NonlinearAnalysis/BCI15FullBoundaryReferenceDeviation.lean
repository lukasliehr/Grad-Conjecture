import BCI14UniformPhysicalBoundaryInverse

noncomputable section
set_option maxHeartbeats 1400000
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

namespace Grad.ActualBoundaryPrimitives.PhysicalBoundaryState
open Grad.ActualBoundaryInverse
variable {parameters : PhaseParameters} {L compact : ℝ}
/-- Ordered subtraction of the reference row on all seven literal inputs. -/
def fullBoundaryDeviation (state : PhysicalBoundaryState parameters L compact) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelAdd
      (fullKernelAdd (fullKernelComposition state.rotatedDeltaRow state.covariant)
        (fullKernelComposition state.deltaRow state.rotatedCovariant))
      (fullKernelSub
        (fullKernelComposition (fullKernelComposition state.massPerturbation state.massInverse) (sevenInputSlotKernel parameters 0))
        (fullKernelComposition state.massInverse state.knownJ)))
end Grad.ActualBoundaryPrimitives.PhysicalBoundaryState

namespace Grad.ActualBoundaryInverse
variable {parameters : PhaseParameters} {L compact : ℝ}

theorem first_rotated_covariant (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition (coordinateProjectionKernel parameters 3 0) state.rotatedCovariant =
      fullKernelComposition state.massInverse (fullKernelSub (sevenInputSlotKernel parameters 0) state.knownJ) := by
  have firstV := actualUnknownVKernel_first_kernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
  have firstKnown := actualKnownRAStarKernel_first_kernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
  unfold PhysicalBoundaryState.rotatedCovariant actualRotatedCovariantKernel
  dsimp only
  rw [fullKernelComposition_add_inner, ← fullKernelComposition_assoc, firstV, fullIdentityKernel_comp_rect,
    firstKnown, fullKernel_add_zero]
  rfl

theorem full_physical_boundary_reference_difference (state : PhysicalBoundaryState parameters L compact) :
    fullKernelAdd state.physicalRow (fullKernelComposition (highAngularKernel parameters 1) (sevenInputSlotKernel parameters 0)) =
      state.fullBoundaryDeviation := by
  have lambdaLaw := actualBoundaryMultiplier_decomposition parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
  have rotatedLaw := actualRotatedBoundaryMultiplier_decomposition parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
  have massSlot := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 =>
    fullKernelComposition kernel (sevenInputSlotKernel parameters 0)) (massInverse_reference_difference state)
  rw [fullKernelComposition_add_outer, fullIdentityKernel_comp_rect] at massSlot
  unfold PhysicalBoundaryState.physicalRow actualDifferentiatedPhysicalBoundaryKernel
  rw [lambdaLaw, rotatedLaw]
  change fullKernelAdd
    (fullKernelComposition (highAngularKernel parameters 1)
      (fullKernelAdd (fullKernelComposition state.rotatedDeltaRow state.covariant)
        (fullKernelComposition (fullKernelAdd state.deltaRow (coordinateProjectionKernel parameters 3 0)) state.rotatedCovariant)))
    (fullKernelComposition (highAngularKernel parameters 1) (sevenInputSlotKernel parameters 0)) = _
  rw [fullKernelComposition_add_outer, first_rotated_covariant, ← fullKernelComposition_add_inner]
  unfold PhysicalBoundaryState.fullBoundaryDeviation
  apply congrArg (fullKernelComposition (highAngularKernel parameters 1))
  rw [fullKernelSub, fullKernelComposition_add_inner, fullKernelComposition_neg_inner]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have massEntry := congrArg (fun kernel : FullTwoFrequencyKernel parameters 7 1 => kernel.entry shift frequency) massSlot
  simp only [fullKernelAdd_entry, fullKernelSub_entry, fullKernelNeg_entry] at massEntry ⊢
  rw [← massEntry]
  abel

theorem fullBoundaryDeviation_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.fullBoundaryDeviation) := by
  unfold PhysicalBoundaryState.fullBoundaryDeviation
  apply BoundaryDeviationMoments.regular_comp (BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1))
  apply UniformKernelMoments.add
  · exact UniformKernelMoments.add
      (BoundaryDeviationMoments.comp_regular (boundaryRotatedDeviationMultiplier_vanishingMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualCovariantKernel_physicalMoments parameters L compact)))
      (BoundaryDeviationMoments.comp_regular (boundaryDeviationMultiplier_vanishingMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualRotatedCovariantKernel_physicalMoments parameters L compact)))
  · exact UniformKernelMoments.sub
      (BoundaryDeviationMoments.comp_regular
        (BoundaryDeviationMoments.comp_regular (actualMassPerturbation_vanishingMoments parameters L compact)
          (BoundaryKernelMoments.of_reconstruction (actualMassInverseKernel_physicalMoments parameters L compact)))
        (BoundaryKernelMoments.fixed parameters L compact (sevenInputSlotKernel parameters 0)))
      (BoundaryDeviationMoments.regular_comp
        (BoundaryKernelMoments.of_reconstruction (actualMassInverseKernel_physicalMoments parameters L compact))
        (actualKnownJStar_vanishingMoments parameters L compact))

/-- AI9's reference row, including unrestricted known source slots. -/
theorem full_physical_boundary_reference (state : PhysicalBoundaryState parameters L compact)
    (reference : state.budget 0 = 0) :
    state.physicalRow = fullKernelNeg (fullKernelComposition (highAngularKernel parameters 1) (sevenInputSlotKernel parameters 0)) := by
  have deviationZero := BoundaryDeviationMoments.reference_zero
    (fullBoundaryDeviation_vanishingMoments parameters L compact) state reference
  have difference := full_physical_boundary_reference_difference state
  rw [deviationZero] at difference
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have entry := congrArg (fun kernel : FullTwoFrequencyKernel parameters 7 1 => kernel.entry shift frequency) difference
  simp only [fullKernelAdd_entry, fullZeroKernel_entry, fullKernelNeg_entry] at entry ⊢
  exact eq_neg_of_add_eq_zero_left entry

theorem reference_known_boundary_slot_zero (state : PhysicalBoundaryState parameters L compact)
    (reference : state.budget 0 = 0) (slot : Fin 7) (known : slot ≠ 0) :
    fullKernelComposition state.physicalRow (coordinateInjectionKernel parameters 7 slot) = fullZeroKernel parameters 1 1 := by
  rw [full_physical_boundary_reference state reference, fullKernelComposition_neg_outer,
    fullKernelComposition_assoc, sevenInputSlotKernel,
    coordinateProjection_injection_distinct parameters 7 0 slot (Ne.symm known), fullKernel_comp_zero, fullKernel_neg_zero]

end Grad.ActualBoundaryInverse
