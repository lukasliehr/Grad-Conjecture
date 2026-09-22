import BCT13BoundedPhysicalBoundary

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

/-- K recovers the actual mean-free angular primitive. No independent
boundary value can be chosen after fixing its genuine derivative. -/
theorem angularInverse_recovers_of_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field derivative : NegativeTrace parameters angular cell dimension)
    (meanFree : IsAngularMeanFree parameters angular cell field)
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    fullNegativeKernelAction parameters angular cell
      (angularInverseKernel parameters dimension) derivative = field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [angularInverseKernel, scalarModeDiagonalKernel_action_coefficient, differentiated mode,
    smul_smul]
  by_cases zero : mode.1 = 0
  · have modeZero : mode = (0, mode.2) := Prod.ext zero rfl
    rw [modeZero, meanFree mode.2, smul_zero]
  · simp only [angularInverseMultiplier, if_neg zero,
      inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)), one_smul]

theorem highBoundaryPrimitiveTrace_injective (parameters : PhaseParameters) (angular cell : ℕ) :
    Function.Injective (highBoundaryPrimitiveTrace parameters angular cell) := by
  intro first second equality
  apply Subtype.ext
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [highBoundaryPrimitive_derivative parameters angular cell first mode,
    highBoundaryPrimitive_derivative parameters angular cell second mode, equality]

/-- Every high trace with a negative-half angular derivative has precisely
the P_R realization prescribed by that derivative. -/
theorem highBoundaryPrimitiveTrace_recovers (parameters : PhaseParameters) (angular cell : ℕ)
    (field derivative : NegativeTrace parameters angular cell 1)
    (fieldHigh : IsHighAngularTrace parameters angular cell field)
    (derivativeHigh : IsHighAngularTrace parameters angular cell derivative)
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    highBoundaryPrimitiveTrace parameters angular cell
      (⟨derivative, derivativeHigh⟩ : HighBoundaryPrimitive parameters angular cell) = field :=
  angularInverse_recovers_of_derivative parameters angular cell field derivative
    fieldHigh.meanFree differentiated

end Grad.ActualBoundaryPrimitives
