import AIA4ExactZeroShiftConsumers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

theorem circularEliminatedXKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularEliminatedXKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularEliminatedBulkKernel, circularEliminatedCKernel, circularEliminatedRVKernel, circularEliminatedXKernel, circularEliminatedSevenKernel, circularEliminationRightHandKernel, circularNormalizedCKernel, circularNormalizedRVKernel, circularRetainedFirstRowKernel, retainedBInverseKernel, eightInputSlotKernel, knownEightToSevenKernel, circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
    ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero]

theorem circularEliminatedCKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularEliminatedCKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularEliminatedBulkKernel, circularEliminatedCKernel, circularEliminatedRVKernel, circularEliminatedXKernel, circularEliminatedSevenKernel, circularEliminationRightHandKernel, circularNormalizedCKernel, circularNormalizedRVKernel, circularRetainedFirstRowKernel, retainedBInverseKernel, eightInputSlotKernel, knownEightToSevenKernel, circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
    ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero]

theorem circularEliminatedRVKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularEliminatedRVKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularEliminatedBulkKernel, circularEliminatedCKernel, circularEliminatedRVKernel, circularEliminatedXKernel, circularEliminatedSevenKernel, circularEliminationRightHandKernel, circularNormalizedCKernel, circularNormalizedRVKernel, circularRetainedFirstRowKernel, retainedBInverseKernel, eightInputSlotKernel, knownEightToSevenKernel, circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
    ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero]

theorem circularEliminatedBulkKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularEliminatedBulkKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularEliminatedBulkKernel, circularEliminatedCKernel, circularEliminatedRVKernel, circularEliminatedXKernel, circularEliminatedSevenKernel, circularEliminationRightHandKernel, circularNormalizedCKernel, circularNormalizedRVKernel, circularRetainedFirstRowKernel, retainedBInverseKernel, eightInputSlotKernel, knownEightToSevenKernel, circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
    ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero]

theorem circularEliminatedXKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 8) :
    (circularEliminatedXKernel parameters L).entry (0, 0) mode value 0 = circularEliminatedXSymbol mode value := by
  obtain ⟨field, coefficient⟩ := exists_negativeTrace_coefficient parameters 0 0 8 mode value
  have exactFormula := circularEliminatedXKernel_action_coefficient parameters L 0 0 field mode
  rw [zeroShift_negativeTrace_coefficient parameters 0 0 _
    (circularEliminatedXKernel_zeroShift parameters L) field mode, coefficient] at exactFormula
  exact exactFormula

theorem circularEliminatedCKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 8) :
    (circularEliminatedCKernel parameters L).entry (0, 0) mode value 0 = -highAngularMultiplier mode * (value 6 + (L : ℂ)⁻¹ * value 2) := by
  obtain ⟨field, coefficient⟩ := exists_negativeTrace_coefficient parameters 0 0 8 mode value
  have exactFormula := circularEliminatedCKernel_action_coefficient parameters L 0 0 field mode
  rw [zeroShift_negativeTrace_coefficient parameters 0 0 _
    (circularEliminatedCKernel_zeroShift parameters L) field mode, coefficient] at exactFormula
  exact exactFormula

theorem circularEliminatedRVKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 8) :
    (circularEliminatedRVKernel parameters L).entry (0, 0) mode value 0 = highAngularMultiplier mode * (-value 1 - 2 * angularInverseMultiplier mode * circularEliminatedXSymbol mode value) := by
  obtain ⟨field, coefficient⟩ := exists_negativeTrace_coefficient parameters 0 0 8 mode value
  have exactFormula := circularEliminatedRVKernel_action_coefficient parameters L 0 0 field mode
  rw [zeroShift_negativeTrace_coefficient parameters 0 0 _
    (circularEliminatedRVKernel_zeroShift parameters L) field mode, coefficient] at exactFormula
  exact exactFormula

theorem circularEliminatedBulkKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 8) :
    (circularEliminatedBulkKernel parameters L).entry (0, 0) mode value =
    WithLp.toLp 2 ![circularEliminatedXSymbol mode value,
      -highAngularMultiplier mode * (value 6 + (L : ℂ)⁻¹ * value 2),
      highAngularMultiplier mode * (-value 1 - 2 * angularInverseMultiplier mode * circularEliminatedXSymbol mode value)] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp only [circularEliminatedBulkKernel, fullKernelAdd_entry,
      kernelComposition_entry_diagonal_inner _ _ (circularEliminatedXKernel_zeroShift parameters L),
      kernelComposition_entry_diagonal_inner _ _ (circularEliminatedCKernel_zeroShift parameters L),
      kernelComposition_entry_diagonal_inner _ _ (circularEliminatedRVKernel_zeroShift parameters L),
      coordinateInjectionKernel, constantMatrixKernel_entry, if_pos rfl, add_apply, ContinuousLinearMap.comp_apply,
      matrixUnit_apply, operatorBasis, circularEliminatedXKernel_entry_zero,
      circularEliminatedCKernel_entry_zero, circularEliminatedRVKernel_entry_zero]
    <;> simp [matrixUnit_apply, operatorBasis, circularEliminatedXKernel_entry_zero,
      circularEliminatedCKernel_entry_zero, circularEliminatedRVKernel_entry_zero]

end Grad.AnnularCircularForm
