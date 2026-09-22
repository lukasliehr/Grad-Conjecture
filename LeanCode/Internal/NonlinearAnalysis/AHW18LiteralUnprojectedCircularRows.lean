import AHW17UnprojectedFirstRowAndContinuity

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

/-- Pre-Q first row on independent RF0, valid also in the angular mean and low modes. -/
theorem circularNormalizedUnprojectedFirstRowKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularNormalizedUnprojectedFirstRowKernel parameters L) input) mode 0 =
      -negativeTraceCoefficient parameters angular cell input mode 0 -
        2 * (2 * angularDoubleInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 0 -
          angularDoubleInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 5 +
          negativeTraceCoefficient parameters angular cell input mode 3) := by
  simp [circularNormalizedUnprojectedFirstRowKernel, circularRetainedForceKernel, fullNegativeKernelAction_comp,
    fullNegativeKernelAction_sub, fullNegativeKernelAction_smul, negativeTraceCoefficient_sub, negativeTraceCoefficient_smul,
    coordinateProjectionKernel_action_coefficient, circularNormalizedCovariantKernel_action_coefficient,
    circularNormalizedRotatedCovariantKernel_action_coefficient, circularCovariantSymbol, circularRotatedCovariantSymbol]
  try ring

/-- The mean-free multiplier stays present before high projection. -/
theorem circularNormalizedUnprojectedCKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularNormalizedUnprojectedCKernel parameters L) input) mode 0 =
      -angularMeanFreeMultiplier mode * (negativeTraceCoefficient parameters angular cell input mode 6 +
        (L : ℂ)⁻¹ * negativeTraceCoefficient parameters angular cell input mode 2) := by
  simp [circularNormalizedUnprojectedCKernel, fullNegativeKernelAction_comp, fullNegativeKernelAction_neg,
    negativeTraceCoefficient_neg, coordinateProjectionKernel_action_coefficient,
    circularNormalizedRotatedCovariantKernel_action_coefficient, circularRotatedCovariantSymbol]
  try ring

/-- The full angular mean of F0 occurs in rV and must not be dropped on the low block. -/
theorem circularNormalizedUnprojectedRVKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularNormalizedUnprojectedRVKernel parameters L) input) mode 0 =
      -negativeTraceCoefficient parameters angular cell input mode 1 -
        2 * angularInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 0 -
        angularMeanMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 4 := by
  simp [circularNormalizedUnprojectedRVKernel, fullNegativeKernelAction_comp, fullNegativeKernelAction_neg,
    fullNegativeKernelAction_add, fullNegativeKernelAction_smul, negativeTraceCoefficient_neg,
    negativeTraceCoefficient_add, negativeTraceCoefficient_smul, sevenInputSlotKernel,
    coordinateProjectionKernel_action_coefficient, circularNormalizedCovariantKernel_action_coefficient, circularCovariantSymbol]
  try ring

end Grad.AnnularReconstruction
