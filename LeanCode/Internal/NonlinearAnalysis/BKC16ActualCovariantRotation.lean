import BKC15ActualReconstructionRotation

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

theorem actualRecoveredMassKernel_action_meanFree
    (input : SevenSlotTrace parameters angular cell)
    (supported : IsAngularMeanFree parameters angular cell (input 0)) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualRecoveredMassKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualRecoveredMassKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply actualMassInverseKernel_action_meanFree
  unfold actualMassRightHandKernel
  rw [fullNegativeKernelAction_sub, sevenInputSlotKernel_action]
  exact supported.sub (actualKnownJStarKernel_action_meanFree parameters L rho alpha
    delta parameter epsilon compactRadius field _ compactNonnegative alphaSmall
    deltaSmall parameterSmall angular cell _)

/-- AH20's reconstructed angular row is the genuine angular derivative of
its covariant row on the literal mean-free x and scalar derivative slots. -/
theorem actualCovariantKernel_derivative
    (input : SevenSlotTrace parameters angular cell)
    (supported : IsAngularMeanFree parameters angular cell (input 0))
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualCovariantKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input))
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedCovariantKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualCovariantKernel actualRotatedCovariantKernel
  dsimp only
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add,
    fullNegativeKernelAction_comp, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply IsAngularDerivative.add
  · apply actualUnknownUKernel_derivative
    exact actualRecoveredMassKernel_action_meanFree parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input supported
  · exact actualKnownAStarKernel_derivative parameters L rho alpha delta parameter
      epsilon compactRadius field _ compactNonnegative alphaSmall deltaSmall
      parameterSmall angular cell input scalarDerivative

end Grad.BoundaryKernelAction
