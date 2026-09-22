import AHW24LiteralKVAndPhysicalV

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

theorem circularEliminatedSevenKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 8) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularEliminatedSevenKernel parameters L) input) mode =
    WithLp.toLp 2 ![circularEliminatedXSymbol mode (negativeTraceCoefficient parameters angular cell input mode),
      negativeTraceCoefficient parameters angular cell input mode 1,
      negativeTraceCoefficient parameters angular cell input mode 2,
      negativeTraceCoefficient parameters angular cell input mode 3,
      negativeTraceCoefficient parameters angular cell input mode 4,
      negativeTraceCoefficient parameters angular cell input mode 5,
      negativeTraceCoefficient parameters angular cell input mode 6] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [circularEliminatedSevenKernel, fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
      negativeTraceCoefficient_add, coordinateInjectionKernel_action_coefficient,
      circularEliminatedXKernel_action_coefficient, knownEightToSevenKernel,
      constantMatrixKernel_action_coefficient, knownEightToSevenMap_apply]

theorem highAngularMultiplier_meanFree (mode : ℤ × ℤ) :
    highAngularMultiplier mode * angularMeanFreeMultiplier mode = highAngularMultiplier mode := by
  by_cases zero : mode.1 = 0
  · simp [highAngularMultiplier, angularMeanFreeMultiplier, zero]
  · simp [angularMeanFreeMultiplier, zero]

theorem highAngularMultiplier_mean (mode : ℤ × ℤ) :
    highAngularMultiplier mode * angularMeanMultiplier mode = 0 := by
  by_cases zero : mode.1 = 0
  · simp [highAngularMultiplier, angularMeanMultiplier, zero]
  · simp [angularMeanMultiplier, zero]

/-- The same eliminated circular c contains precisely the original F2 and xi_zeta slots. -/
theorem circularEliminatedCKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 8) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularEliminatedCKernel parameters L) input) mode 0 =
    -highAngularMultiplier mode * (negativeTraceCoefficient parameters angular cell input mode 6 +
      (L : ℂ)⁻¹ * negativeTraceCoefficient parameters angular cell input mode 2) := by
  unfold circularEliminatedCKernel circularNormalizedCKernel
  rw [fullKernelComposition_assoc]
  change negativeTraceCoefficient parameters angular cell
    (fullNegativeKernelAction parameters angular cell
      (fullKernelComposition (highAngularKernel parameters 1)
        (fullKernelComposition (circularNormalizedUnprojectedCKernel parameters L)
          (circularEliminatedSevenKernel parameters L))) input) mode 0 = _
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, highAngularKernel_coefficient,
    PiLp.smul_apply, smul_eq_mul, circularNormalizedUnprojectedCKernel_action_coefficient,
    circularEliminatedSevenKernel_action_coefficient, Matrix.cons_val ]
  have identity := highAngularMultiplier_meanFree mode
  linear_combination -(negativeTraceCoefficient parameters angular cell input mode 6 +
    (L : ℂ)⁻¹ * negativeTraceCoefficient parameters angular cell input mode 2) * identity

/-- The source F0 mean is removed only by the actual final high projection. -/
theorem circularEliminatedRVKernel_action_coefficient (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 8) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (circularEliminatedRVKernel parameters L) input) mode 0 =
    highAngularMultiplier mode * (-negativeTraceCoefficient parameters angular cell input mode 1 -
      2 * angularInverseMultiplier mode * circularEliminatedXSymbol mode
        (negativeTraceCoefficient parameters angular cell input mode)) := by
  unfold circularEliminatedRVKernel circularNormalizedRVKernel
  rw [fullKernelComposition_assoc]
  change negativeTraceCoefficient parameters angular cell
    (fullNegativeKernelAction parameters angular cell
      (fullKernelComposition (highAngularKernel parameters 1)
        (fullKernelComposition (circularNormalizedUnprojectedRVKernel parameters L)
          (circularEliminatedSevenKernel parameters L))) input) mode 0 = _
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, highAngularKernel_coefficient,
    PiLp.smul_apply, smul_eq_mul, circularNormalizedUnprojectedRVKernel_action_coefficient,
    circularEliminatedSevenKernel_action_coefficient, Matrix.cons_val, Matrix.cons_val_zero ]
  have identity := highAngularMultiplier_mean mode
  linear_combination -(negativeTraceCoefficient parameters angular cell input mode 4) * identity

end Grad.AnnularReconstruction
