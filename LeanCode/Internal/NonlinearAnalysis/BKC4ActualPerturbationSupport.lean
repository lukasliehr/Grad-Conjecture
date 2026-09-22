import BKC3SupportAlgebra

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

theorem actualEncodedE0Kernel_action_support
    (input : NegativeTrace parameters angular cell 3) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedE0Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualEncodedE0Kernel firstCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp]
  apply coordinateInjectionKernel_action_encoded_zero
  rw [fullNegativeKernelAction_comp]
  exact angularMeanKernel_action_constant parameters angular cell _

theorem actualEncodedE1Kernel_action_support
    (input : NegativeTrace parameters angular cell 3) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedE1Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualEncodedE1Kernel secondCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp]
  apply coordinateInjectionKernel_action_encoded_one
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

theorem actualEncodedE2Kernel_action_support
    (input : NegativeTrace parameters angular cell 3) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedE2Kernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualEncodedE2Kernel thirdCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp]
  apply coordinateInjectionKernel_action_encoded_two
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

theorem actualEncodedPerturbationKernel_action_support
    (input : NegativeTrace parameters angular cell 3) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedPerturbationKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualEncodedPerturbationKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add]
  exact (actualEncodedE0Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input).add
    ((actualEncodedE1Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input).add
      (actualEncodedE2Kernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input))

end Grad.BoundaryKernelAction
