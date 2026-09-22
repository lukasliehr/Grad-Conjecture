import AHW6OriginalPhysicalFirstRowConsumer

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal independent ambient source formula: RF0 remains a separate slot. -/
def circularEliminatedXSymbol (mode : ℤ × ℤ) (input : ComplexEuclidean 8) : ℂ :=
  -retainedBInverseMultiplier mode * highAngularMultiplier mode *
    (input 0 + 2 * input 3 - 2 * angularDoubleInverseMultiplier mode * input 5 - input 7)

theorem circularRetainedFirstRowKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularRetainedFirstRowKernel parameters L) input) mode 0 =
    highAngularMultiplier mode *
      (-negativeTraceCoefficient parameters angular cell input mode 0 -
        2 * (2 * angularDoubleInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 0 -
          angularDoubleInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 5 +
          negativeTraceCoefficient parameters angular cell input mode 3)) := by
  simp [circularRetainedFirstRowKernel, circularRetainedForceKernel, fullNegativeKernelAction_comp,
    fullNegativeKernelAction_sub, fullNegativeKernelAction_smul, highAngularKernel_coefficient,
    negativeTraceCoefficient_sub, negativeTraceCoefficient_smul,
    coordinateProjectionKernel_action_coefficient, circularNormalizedCovariantKernel_action_coefficient,
    circularNormalizedRotatedCovariantKernel_action_coefficient, circularCovariantSymbol, circularRotatedCovariantSymbol]
  ring

theorem highAngularMultiplier_sq (mode : ℤ × ℤ) :
    highAngularMultiplier mode * highAngularMultiplier mode = highAngularMultiplier mode := by
  unfold highAngularMultiplier
  split_ifs <;> norm_num

theorem circularEliminatedXKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 8) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularEliminatedXKernel parameters L) input) mode 0 =
      circularEliminatedXSymbol mode (negativeTraceCoefficient parameters angular cell input mode) := by
  simp only [circularEliminatedXKernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_neg, negativeTraceCoefficient_neg, retainedBInverseKernel,
    scalarModeDiagonalKernel_action_coefficient, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    circularEliminationRightHandKernel, fullNegativeKernelAction_sub, highAngularKernel_coefficient,
    negativeTraceCoefficient_sub, PiLp.sub_apply, eightInputSlotKernel, coordinateProjectionKernel_action_coefficient,
    circularRetainedFirstRowKernel_action_coefficient, knownEightToSevenKernel,
    constantMatrixKernel_action_coefficient, knownEightToSevenMap_apply, circularEliminatedXSymbol]
  simp
  by_cases high : 3 ≤ |mode.1|
  · simp only [highAngularMultiplier, if_pos high, mul_one, one_mul]
    ring
  · simp only [highAngularMultiplier, if_neg high, mul_zero, zero_mul]

/-- The only simplification from RF0 to F0 uses the genuine angular derivative. -/
theorem angularDoubleInverse_times_angular (mode : ℤ × ℤ) :
    angularDoubleInverseMultiplier mode * (Complex.I * (mode.1 : ℂ)) = angularInverseMultiplier mode := by
  by_cases zero : mode.1 = 0
  · simp [angularDoubleInverseMultiplier, angularInverseMultiplier, zero]
  · have nonzero : Complex.I * (mode.1 : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)
    simp only [angularDoubleInverseMultiplier, angularInverseMultiplier, if_neg zero]
    rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]

theorem circularEliminatedXKernel_genuineSourceDerivative (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 8)
    (derivative : IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell (eightInputSlotKernel parameters 4) input)
      (fullNegativeKernelAction parameters angular cell (eightInputSlotKernel parameters 5) input))
    (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularEliminatedXKernel parameters L) input) mode 0 =
      -retainedBInverseMultiplier mode * highAngularMultiplier mode *
        (negativeTraceCoefficient parameters angular cell input mode 0 +
          2 * negativeTraceCoefficient parameters angular cell input mode 3 -
          2 * angularInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 4 -
          negativeTraceCoefficient parameters angular cell input mode 7) := by
  have relation := congrArg (fun value : ComplexEuclidean 1 => value 0) (derivative mode)
  simp only [eightInputSlotKernel, coordinateProjectionKernel_action_coefficient, PiLp.smul_apply, smul_eq_mul] at relation
  rw [circularEliminatedXKernel_action_coefficient]
  unfold circularEliminatedXSymbol
  rw [relation]
  have term : 2 * angularDoubleInverseMultiplier mode *
      (Complex.I * (mode.1 : ℂ) * negativeTraceCoefficient parameters angular cell input mode 4) =
      2 * angularInverseMultiplier mode * negativeTraceCoefficient parameters angular cell input mode 4 := by
    calc
      _ = 2 * (angularDoubleInverseMultiplier mode * (Complex.I * (mode.1 : ℂ))) *
          negativeTraceCoefficient parameters angular cell input mode 4 := by ring
      _ = _ := by rw [angularDoubleInverse_times_angular]
  rw [term]

end Grad.AnnularReconstruction
