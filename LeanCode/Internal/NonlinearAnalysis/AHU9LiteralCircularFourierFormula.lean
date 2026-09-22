import AHU8ActualNormalizedReconstructionErrors

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal circular symbol on independent seven-slot data; slot 5 is RF0. -/
def circularCovariantSymbol (L : ℝ) (mode : ℤ × ℤ) (value : ComplexEuclidean 7) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![ -angularInverseMultiplier mode * value 0 - (2 : ℂ)⁻¹ * angularMeanMultiplier mode * value 4,
      2 * angularDoubleInverseMultiplier mode * value 0 - angularDoubleInverseMultiplier mode * value 5 + value 3,
      angularInverseMultiplier mode * (value 6 + (L : ℂ)⁻¹ * value 2)]

theorem circularNormalizedCovariantKernel_action_coefficient
    (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularNormalizedCovariantKernel parameters L) input) mode =
    circularCovariantSymbol L mode (negativeTraceCoefficient parameters angular cell input mode) := by
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [circularNormalizedCovariantKernel, circularUnknownUKernel,       circularRecoveredMassKernel, circularKnownAStarKernel,       circularKnownWKernel, circularUnknownWKernel, circularKnownEncodedDataKernel, circularUnknownNKernel,
      fullNegativeKernelAction_comp, fullNegativeKernelAction_add, fullNegativeKernelAction_neg,
      fullNegativeKernelAction_smul, fullNegativeKernelAction_identity, negativeTraceCoefficient_add,
      negativeTraceCoefficient_neg, negativeTraceCoefficient_smul,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateInjectionKernel_action_coefficient, coordinateProjectionKernel_action_coefficient,
      sevenInputSlotKernel, encodedD0InverseKernel, constantMatrixKernel_action_coefficient,
      encodedJKernel, angularMeanComponentKernel, angularInverseComponentKernel,
      angularDoubleInverseComponentKernel, componentModeKernel_action_coefficient,
      actualUnknownQAKernel, angularInverseKernel, angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
      circularCovariantSymbol, diagonalThreeMap, matrixUnit_apply, operatorBasis]
    <;> (try unfold angularMeanMultiplier) <;> (try split_ifs) <;> ring

/-- Literal circular symbol on independent seven-slot data; slot 5 is RF0. -/
def circularRotatedCovariantSymbol (L : ℝ) (mode : ℤ × ℤ) (value : ComplexEuclidean 7) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![ -value 0,
      2 * angularInverseMultiplier mode * value 0 - angularInverseMultiplier mode * value 5 + value 1,
      angularMeanFreeMultiplier mode * (value 6 + (L : ℂ)⁻¹ * value 2)]

theorem circularNormalizedRotatedCovariantKernel_action_coefficient
    (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularNormalizedRotatedCovariantKernel parameters L) input) mode =
    circularRotatedCovariantSymbol L mode (negativeTraceCoefficient parameters angular cell input mode) := by
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [circularNormalizedRotatedCovariantKernel, circularUnknownVKernel,
      circularRecoveredMassKernel, circularKnownRAStarKernel,
      circularKnownWKernel, circularUnknownWKernel, circularKnownEncodedDataKernel, circularUnknownNKernel,
      fullNegativeKernelAction_comp, fullNegativeKernelAction_add, fullNegativeKernelAction_neg,
      fullNegativeKernelAction_smul, fullNegativeKernelAction_identity, negativeTraceCoefficient_add,
      negativeTraceCoefficient_neg, negativeTraceCoefficient_smul,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateInjectionKernel_action_coefficient, coordinateProjectionKernel_action_coefficient,
      sevenInputSlotKernel, encodedD0InverseKernel, constantMatrixKernel_action_coefficient,
      encodedRotationKernel, angularInverseComponentKernel,
      angularMeanFreeComponentKernel, componentModeKernel_action_coefficient,
      angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
      circularRotatedCovariantSymbol, diagonalThreeMap, matrixUnit_apply, operatorBasis]
    <;> ring

end Grad.AnnularReconstruction
