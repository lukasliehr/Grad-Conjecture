import AHW21GenuineCofactorAngularProduct

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

theorem circularNormalizedUnprojectedFirstRowKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 7) :
    (circularNormalizedUnprojectedFirstRowKernel parameters L).entry (0, 0) mode value 0 =
      -value 0 - 2 * (2 * angularDoubleInverseMultiplier mode * value 0 - angularDoubleInverseMultiplier mode * value 5 + value 3) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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
  simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, smul_apply, ContinuousLinearMap.id_apply,
      PiLp.neg_apply]
  simp [diagonalThreeMap, matrixUnit_apply, operatorBasis]
  ring

theorem circularNormalizedUnprojectedFirstRowKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularNormalizedUnprojectedFirstRowKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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

theorem circularNormalizedUnprojectedCKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 7) :
    (circularNormalizedUnprojectedCKernel parameters L).entry (0, 0) mode value 0 =
      -angularMeanFreeMultiplier mode * (value 6 + (L : ℂ)⁻¹ * value 2) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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
  simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, smul_apply, ContinuousLinearMap.id_apply,
      PiLp.neg_apply]
  simp [diagonalThreeMap, matrixUnit_apply, operatorBasis]
  ring

theorem circularNormalizedUnprojectedCKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularNormalizedUnprojectedCKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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

theorem circularNormalizedUnprojectedRVKernel_entry_zero (parameters : PhaseParameters) (L : ℝ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 7) :
    (circularNormalizedUnprojectedRVKernel parameters L).entry (0, 0) mode value 0 =
      -value 1 - 2 * angularInverseMultiplier mode * value 0 - angularMeanMultiplier mode * value 4 := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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
  simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, smul_apply, ContinuousLinearMap.id_apply,
      PiLp.neg_apply]
  simp [diagonalThreeMap, matrixUnit_apply, operatorBasis]
  by_cases zero : mode.1 = 0 <;> simp [angularMeanMultiplier, zero] <;> ring

theorem circularNormalizedUnprojectedRVKernel_zeroShift (parameters : PhaseParameters) (L : ℝ) :
    ZeroShiftKernel (circularNormalizedUnprojectedRVKernel parameters L) := by
  simp (config := { maxDischargeDepth := 100 }) only [circularNormalizedUnprojectedFirstRowKernel, circularNormalizedUnprojectedCKernel, circularNormalizedUnprojectedRVKernel, circularRetainedForceKernel,
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

end Grad.AnnularReconstruction
