import BKC5InverseSupportAlgebra

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

section Preconditioned

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

theorem actualPreconditionedEncodedPerturbationKernel_action_support
    (input : NegativeTrace parameters angular cell 3) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualPreconditionedEncodedPerturbationKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply encodedD0InverseKernel_action_support
  exact actualEncodedPerturbationKernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input

end Preconditioned

section Inverse

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

 theorem actualEncodedIdentityInverseKernel_action_support
    (input : NegativeTrace parameters angular cell 3)
    (supported : EncodedSupport parameters angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  apply fullPositiveIdentityInverse_action_support parameters angular cell
    (EncodedSupport parameters angular cell) (fun first second => first.sub second)
    _ _ (actualEncodedIdentityInverseKernel_right parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    _ input supported
  intro argument
  exact actualPreconditionedEncodedPerturbationKernel_action_support
    parameters L rho alpha delta parameter epsilon compactRadius field _
    compactNonnegative alphaSmall deltaSmall parameterSmall angular cell argument

/-- AE24's actual Neumann inverse preserves AE14's literal supports. -/
theorem actualEncodedFirstInverseKernel_action_support
    (input : NegativeTrace parameters angular cell 3)
    (supported : EncodedSupport parameters angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualEncodedFirstInverseKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualEncodedFirstInverseKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply actualEncodedIdentityInverseKernel_action_support parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
  exact encodedD0InverseKernel_action_support parameters angular cell input supported

end Inverse

end Grad.BoundaryKernelAction
