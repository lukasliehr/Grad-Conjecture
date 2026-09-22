import BKC16ActualCovariantRotation

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

 theorem actualForceBoundaryKernel_derivative
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (angular cell : ℕ) (input derivative : NegativeTrace parameters angular cell 3)
    (differentiated : IsAngularDerivative parameters angular cell input derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualForceBoundaryKernel parameters L rho epsilon field kind low) input)
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedForceBoundaryKernel parameters L rho epsilon field kind low) input +
       fullNegativeKernelAction parameters angular cell
        (actualForceBoundaryKernel parameters L rho epsilon field kind low) derivative) :=
  boundaryRowMultiplicationKernel_derivative parameters angular cell 3 _ _ _
    input derivative differentiated

 theorem IsAngularConstant.neg {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field : NegativeTrace parameters angular cell dimension}
    (supported : IsAngularConstant parameters angular cell field) :
    IsAngularConstant parameters angular cell (-field) := by
  intro mode nonzero
  rw [negativeTraceCoefficient_neg, supported mode nonzero, neg_zero]

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

theorem actualUnknownN0Kernel_action_support
    (input : NegativeTrace parameters angular cell 1) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownN0Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownN0Kernel firstCoordinateInjectionKernel
  dsimp only
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_zero
  rw [fullNegativeKernelAction_neg]
  apply IsAngularConstant.neg
  rw [fullNegativeKernelAction_comp]
  exact angularMeanKernel_action_constant parameters angular cell _

/-- AF5's unprojected middle row really has mean zero: its parenthesized
expression is the derivative of the actual force coefficient product. -/
theorem actualUnknownN1Kernel_action_support
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownN1Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownN1Kernel secondCoordinateInjectionKernel
  dsimp only
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_one
  rw [fullNegativeKernelAction_sub, fullNegativeKernelAction_smul,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply]
  apply (supported.smul 2).sub
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  have differentiated := actualGaugeQKernelOnBall_derivative parameters L rho alpha
    delta parameter epsilon compactRadius field
      ((physicalBudget_monotone parameters field rho epsilon (by omega : 6 ≤ 7)).trans
        (small.trans (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)))
      compactNonnegative alphaSmall deltaSmall parameterSmall angular cell _ _
      (actualUnknownQAKernel_derivative parameters angular cell input supported)
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  exact (actualForceBoundaryKernel_derivative parameters L rho epsilon field 0 _
    angular cell _ _ differentiated).meanFree

 theorem actualUnknownN2Kernel_action_support
    (input : NegativeTrace parameters angular cell 1) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownN2Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownN2Kernel thirdCoordinateInjectionKernel
  dsimp only
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_two
  rw [fullNegativeKernelAction_neg]
  apply IsAngularMeanFree.neg
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

 theorem actualUnknownNKernel_action_support
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownNKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownNKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add]
  exact (actualUnknownN0Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input).add
    ((actualUnknownN1Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input supported).add
      (actualUnknownN2Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input))

 theorem actualUnknownWKernel_action_support
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualUnknownWKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply actualEncodedFirstInverseKernel_action_support
  exact actualUnknownNKernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input supported

 theorem actualKnownEncodedWKernel_action_support
    (input : SevenSlotTrace parameters angular cell)
    (supported : KnownSevenSlotSupport parameters L angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedWKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownEncodedWKernel
  dsimp only
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply actualEncodedFirstInverseKernel_action_support
  exact actualKnownEncodedDataKernel_action_support parameters L rho alpha delta
    parameter epsilon compactRadius field _ compactNonnegative alphaSmall deltaSmall
    parameterSmall angular cell input supported

end Grad.BoundaryKernelAction
