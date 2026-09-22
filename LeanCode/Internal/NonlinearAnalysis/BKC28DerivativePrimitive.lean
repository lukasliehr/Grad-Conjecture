import BKC18PhysicalRotationConsumer

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

theorem angularMeanFreeKernel_action_eq {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension)
    (supported : IsAngularMeanFree parameters angular cell field) :
    fullNegativeKernelAction parameters angular cell
      (angularMeanFreeKernel parameters dimension) field = field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [angularMeanFreeKernel, scalarModeDiagonalKernel_action_coefficient]
  by_cases zero : mode.1 = 0
  · have equality : mode = (0, mode.2) := Prod.ext zero rfl
    rw [equality, supported]
    exact smul_zero _
  · simp only [angularMeanFreeMultiplier, if_neg zero, one_smul]

theorem IsAngularDerivative.scalarMode {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) field)
      (fullNegativeKernelAction parameters angular cell
        (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) derivative) := by
  intro mode
  rw [scalarModeDiagonalKernel_action_coefficient, scalarModeDiagonalKernel_action_coefficient,
    differentiated mode]
  exact smul_comm _ _ _

theorem IsAngularDerivative.meanFreeProjection {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (angularMeanFreeKernel parameters dimension) field) derivative := by
  have projected := differentiated.scalarMode angularMeanFreeMultiplier 1
    angularMeanFreeMultiplier_norm_le
  change IsAngularDerivative parameters angular cell
    (fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters dimension) field)
    (fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters dimension) derivative)
      at projected
  rw [angularMeanFreeKernel_action_eq parameters angular cell derivative differentiated.meanFree]
    at projected
  exact projected

/-- KR=P on the original mean-free completed trace. No cell frequency is
divided, and the angular zero mode is handled by its actual support. -/
theorem IsAngularDerivative.primitive {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative)
    (supported : IsAngularMeanFree parameters angular cell field) :
    fullNegativeKernelAction parameters angular cell
      (angularInverseKernel parameters dimension) derivative = field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [angularInverseKernel, scalarModeDiagonalKernel_action_coefficient,
    differentiated mode, smul_smul, mul_comm (angularInverseMultiplier mode),
    angularFrequency_mul_inverse]
  by_cases zero : mode.1 = 0
  · have equality : mode = (0, mode.2) := Prod.ext zero rfl
    rw [equality, supported]
    exact smul_zero _
  · simp only [angularMeanFreeMultiplier, if_neg zero, one_smul]

theorem IsAngularDerivative.unique_meanFree {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first second derivative : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularDerivative parameters angular cell first derivative)
    (hsecond : IsAngularDerivative parameters angular cell second derivative)
    (firstSupported : IsAngularMeanFree parameters angular cell first)
    (secondSupported : IsAngularMeanFree parameters angular cell second) :
    first = second :=
  (hfirst.primitive firstSupported).symm.trans (hsecond.primitive secondSupported)

end Grad.BoundaryKernelAction
