import BKC11ActualGaugeSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- The genuine weak angular derivative relation in the complete original
Fourier coordinates. It contains no independent coefficient-row premise. -/
def IsAngularDerivative {dimension : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (field derivative : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ mode, negativeTraceCoefficient parameters angular cell derivative mode =
    (Complex.I * (mode.1 : ℂ)) • negativeTraceCoefficient parameters angular cell field mode

theorem IsAngularDerivative.meanFree {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularMeanFree parameters angular cell derivative := by
  intro axial
  rw [differentiated]
  simp

theorem IsAngularDerivative.add {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first firstDerivative second secondDerivative : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularDerivative parameters angular cell first firstDerivative)
    (hsecond : IsAngularDerivative parameters angular cell second secondDerivative) :
    IsAngularDerivative parameters angular cell (first + second) (firstDerivative + secondDerivative) := by
  intro mode
  rw [negativeTraceCoefficient_add, negativeTraceCoefficient_add, hfirst, hsecond, smul_add]

theorem IsAngularDerivative.neg {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularDerivative parameters angular cell (-field) (-derivative) := by
  intro mode
  rw [negativeTraceCoefficient_neg, negativeTraceCoefficient_neg, differentiated, smul_neg]

theorem IsAngularDerivative.sub {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first firstDerivative second secondDerivative : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularDerivative parameters angular cell first firstDerivative)
    (hsecond : IsAngularDerivative parameters angular cell second secondDerivative) :
    IsAngularDerivative parameters angular cell (first - second) (firstDerivative - secondDerivative) := by
  simpa only [sub_eq_add_neg] using hfirst.add hsecond.neg

theorem IsAngularDerivative.add_constant {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative constant : NegativeTrace parameters angular cell dimension}
    (differentiated : IsAngularDerivative parameters angular cell field derivative)
    (supported : IsAngularConstant parameters angular cell constant) :
    IsAngularDerivative parameters angular cell (field + constant) derivative := by
  intro mode
  rw [negativeTraceCoefficient_add, smul_add, differentiated mode]
  by_cases zero : mode.1 = 0
  · simp only [zero, Int.cast_zero, mul_zero, zero_smul, add_zero]
  · rw [supported mode zero, smul_zero, add_zero]

theorem IsAngularDerivative.constantMatrix {input output : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field derivative : NegativeTrace parameters angular cell input}
    (differentiated : IsAngularDerivative parameters angular cell field derivative)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (constantMatrixKernel parameters input output mapping) field)
      (fullNegativeKernelAction parameters angular cell
        (constantMatrixKernel parameters input output mapping) derivative) := by
  intro mode
  rw [constantMatrixKernel_action_coefficient, constantMatrixKernel_action_coefficient,
    differentiated mode, map_smul]

theorem angularFrequency_mul_inverse (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) * angularInverseMultiplier mode =
      angularMeanFreeMultiplier mode := by
  by_cases zero : mode.1 = 0
  · simp [angularInverseMultiplier, angularMeanFreeMultiplier, zero]
  · simp only [angularInverseMultiplier, angularMeanFreeMultiplier, if_neg zero]
    exact mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero))

theorem angularFrequency_mul_doubleInverse (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) * angularDoubleInverseMultiplier mode =
      angularInverseMultiplier mode := by
  rw [angularDoubleInverseMultiplier, ← mul_assoc, angularFrequency_mul_inverse]
  by_cases zero : mode.1 = 0
  · simp [angularMeanFreeMultiplier, angularInverseMultiplier, zero]
  · simp only [angularMeanFreeMultiplier, if_neg zero, one_mul]

theorem angularFrequency_mul_mean (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) * angularMeanMultiplier mode = 0 := by
  by_cases zero : mode.1 = 0 <;> simp [angularMeanMultiplier, zero]

theorem angularInverseKernel_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension)
    (supported : IsAngularMeanFree parameters angular cell field) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (angularInverseKernel parameters dimension) field) field := by
  intro mode
  rw [angularInverseKernel, scalarModeDiagonalKernel_action_coefficient,
    smul_smul, angularFrequency_mul_inverse]
  by_cases zero : mode.1 = 0
  · have equality : mode = (0, mode.2) := Prod.ext zero rfl
    rw [equality, supported]
    simp only [smul_zero]
  · simp only [angularMeanFreeMultiplier, if_neg zero, one_smul]

end Grad.BoundaryKernelAction
