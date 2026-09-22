import BCT11CompleteBoundaryPrimitive
import BKC12AngularDerivativePairs

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

theorem highAngularKernel_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (highAngularKernel parameters dimension) field) mode =
      highAngularMultiplier mode • negativeTraceCoefficient parameters angular cell field mode :=
  scalarModeDiagonalKernel_action_coefficient parameters angular cell _ _ _ field mode

theorem highAngularKernel_high {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) :
    IsHighAngularTrace parameters angular cell
      (fullNegativeKernelAction parameters angular cell (highAngularKernel parameters dimension) field) := by
  intro mode low
  rw [highAngularKernel_coefficient]
  simp only [highAngularMultiplier, if_neg (not_le.mpr low), zero_smul]

theorem IsHighAngularTrace.meanFree {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field : NegativeTrace parameters angular cell dimension}
    (supported : IsHighAngularTrace parameters angular cell field) :
    IsAngularMeanFree parameters angular cell field := by
  intro axial
  exact supported (0, axial) (by norm_num)

theorem highAngularKernel_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field derivative : NegativeTrace parameters angular cell dimension)
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell (highAngularKernel parameters dimension) field)
      (fullNegativeKernelAction parameters angular cell (highAngularKernel parameters dimension) derivative) := by
  intro mode
  rw [highAngularKernel_coefficient, highAngularKernel_coefficient, differentiated mode]
  exact smul_comm _ _ _

theorem highBoundaryPrimitive_derivative (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    IsAngularDerivative parameters angular cell
      (highBoundaryPrimitiveTrace parameters angular cell field) field.val :=
  angularInverseKernel_derivative parameters angular cell field.val
    (IsHighAngularTrace.meanFree field.property)

theorem highBoundaryPrimitiveTrace_high (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    IsHighAngularTrace parameters angular cell
      (highBoundaryPrimitiveTrace parameters angular cell field) := by
  intro mode low
  rw [highBoundaryPrimitiveTrace, angularInverseKernel, scalarModeDiagonalKernel_action_coefficient,
    field.property mode low, smul_zero]

/-- The literal AH16 P_R Fourier norm, including the original phase,
split tangential powers, and negative half power of 1+|m|+|n|. -/
theorem highBoundaryPrimitive_norm_sq (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      negativeTraceWeightSq parameters angular cell mode * |(mode.1 : ℝ)| ^ 2 *
        ‖negativeTraceCoefficient parameters angular cell
          (highBoundaryPrimitiveTrace parameters angular cell field) mode‖ ^ 2 := by
  rw [highBoundaryPrimitive_norm, negativeTrace_norm_sq]
  apply tsum_congr
  intro mode
  rw [highBoundaryPrimitive_derivative parameters angular cell field mode,
    norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow]
  ring

end Grad.ActualBoundaryPrimitives
