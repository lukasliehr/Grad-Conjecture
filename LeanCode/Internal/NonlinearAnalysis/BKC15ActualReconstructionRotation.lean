import BKC14ConvolutionDerivative

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem actualUnknownQAKernel_derivative (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell (actualUnknownQAKernel parameters) input)
      (fullNegativeKernelAction parameters angular cell (firstCoordinateInjectionKernel parameters) input) := by
  unfold actualUnknownQAKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  exact (angularInverseKernel_derivative parameters angular cell input supported).constantMatrix _

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

/-- AF6 with the derivative proved from the actual gauge correction and K,
not supplied as an independent row hypothesis. -/
theorem actualUnknownUKernel_derivative
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownUKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input)
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownVKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownUKernel actualUnknownVKernel
  dsimp only
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add]
  apply actualGaugeQKernelOnBall_derivative
  exact (encodedJKernel_derivative parameters angular cell _).add
    (actualUnknownQAKernel_derivative parameters angular cell input supported)

/-- AF7's genuine known derivative on the literal AH20 scalar/rotation slots. -/
theorem actualKnownAStarKernel_derivative
    (input : SevenSlotTrace parameters angular cell)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownAStarKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input))
      (fullNegativeKernelAction parameters angular cell
        (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownAStarKernel actualKnownRAStarKernel actualKnownRotatedQStarKernel
  dsimp only
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action]
  apply actualGaugeQKernelOnBall_derivative
  exact (encodedJKernel_derivative parameters angular cell _).add
    (scalarDerivative.constantMatrix _)

end Grad.BoundaryKernelAction
