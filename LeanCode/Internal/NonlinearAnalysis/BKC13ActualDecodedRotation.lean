import BKC12AngularDerivativePairs

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

/-- AE16's actual encoded derivative. The ambient extension of J already
contains the exact projections, so this identity holds on every input. -/
theorem encodedJKernel_derivative (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 3) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell (encodedJKernel parameters) field)
      (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) field) := by
  intro mode
  apply PiLp.ext
  intro coordinate
  simp only [encodedRotationKernel, encodedJKernel, fullNegativeKernelAction_add,
    negativeTraceCoefficient_add, PiLp.add_apply, angularInverseComponentKernel,
    angularMeanFreeComponentKernel, angularMeanComponentKernel,
    angularDoubleInverseComponentKernel, componentModeKernel_action_coefficient,
    PiLp.smul_apply, smul_eq_mul]
  fin_cases coordinate
  · norm_num [Fin.ext_iff]
    by_cases zero : mode.1 = 0
    · exact Or.inl zero
    · exact Or.inr (Or.inl (by simp [angularMeanMultiplier, zero]))
  · norm_num [Fin.ext_iff]
    rw [← mul_assoc, angularFrequency_mul_doubleInverse]
  · norm_num [Fin.ext_iff]
    rw [← mul_assoc, angularFrequency_mul_inverse]

/-- The actual gauge correction has zero angular derivative; consequently
the original input derivative is the derivative of Q applied to that input. -/
theorem actualGaugeQKernelOnBall_derivative
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ) (input derivative : NegativeTrace parameters angular cell 3)
    (differentiated : IsAngularDerivative parameters angular cell input derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        input) derivative := by
  unfold actualGaugeQKernelOnBall
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_identity,
    ContinuousLinearMap.id_apply]
  exact differentiated.add_constant
    (actualGaugeCorrectionKernelOnBall_action_constant parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall angular cell input)

theorem positiveToNegative_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension) :
    IsAngularDerivative parameters angular cell
      (positiveToNegative parameters angular cell field)
      (positiveRotationToNegative parameters angular cell field) := by
  intro mode
  rw [positiveToNegative_coefficient, positiveRotationToNegative_coefficient]

end Grad.BoundaryKernelAction
