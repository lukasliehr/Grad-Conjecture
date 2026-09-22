import BKC7SevenSlotSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

/-- The actual Neumann inverse of -I+T preserves angular mean zero whenever
T has mean-free range. This follows from its checked inverse equation. -/
theorem fullNegativeIdentityInverse_action_meanFree {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1)
    (range : ∀ input, IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell kernel input))
    (field : NegativeTrace parameters angular cell dimension)
    (supported : IsAngularMeanFree parameters angular cell field) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall) field) := by
  have equation := congrArg (fun mapping => mapping field)
    (fullNegativeKernelAction_inverse_right parameters angular cell kernel low lowBound lowSmall)
  change fullNegativeKernelAction parameters angular cell
      (fullKernelNegativeIdentityPerturbation parameters kernel)
      (fullNegativeKernelAction parameters angular cell
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall) field) = field
    at equation
  rw [fullKernelNegativeIdentityPerturbation, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] at equation
  have rearranged := eq_sub_of_add_eq
    ((add_comm _ _).trans (sub_eq_iff_eq_add.mp equation).symm)
  rw [rearranged]
  exact (range _).sub supported

section FirstBall

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

theorem actualMassPerturbationKernel_action_meanFree
    (input : NegativeTrace parameters angular cell 1) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualMassPerturbationKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualMassPerturbationKernel
  dsimp only
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

theorem actualKnownJStarKernel_action_meanFree
    (input : NegativeTrace parameters angular cell 7) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownJStarKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualKnownJStarKernel
  dsimp only
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

end FirstBall

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

theorem actualMassInverseKernel_action_meanFree
    (input : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell input) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualMassInverseKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) := by
  unfold actualMassInverseKernel
  dsimp only
  apply fullNegativeIdentityInverse_action_meanFree parameters angular cell
    _ _ _ _ _ input supported
  intro argument
  exact actualMassPerturbationKernel_action_meanFree parameters L rho alpha delta
    parameter epsilon compactRadius field _ compactNonnegative alphaSmall deltaSmall
    parameterSmall angular cell argument

end Grad.BoundaryKernelAction
