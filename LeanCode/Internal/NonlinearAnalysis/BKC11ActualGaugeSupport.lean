import BKC10AngularDiagonalAlgebra

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives Grad.SourceCollarCoefficients

theorem actualGammaDeviationKernel_angularDiagonal
    (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    AngularDiagonalKernel
      (actualGammaDeviationKernel parameters L rho alpha delta parameter epsilon field low) := by
  intro shift frequency nonzero
  unfold actualGammaDeviationKernel
  apply ContinuousLinearMap.ext
  intro value
  rw [boundaryMatrixMultiplicationKernel_entry_apply]
  simp [actualGammaDeviationCoefficients, nonzero]

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)

theorem actualNegativeGammaInverseKernelOnBall_angularDiagonal :
    AngularDiagonalKernel
      (actualNegativeGammaInverseKernelOnBall parameters L rho alpha delta parameter
        epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall) := by
  unfold actualNegativeGammaInverseKernelOnBall actualNegativeGammaInverseKernel
  apply AngularDiagonalKernel.negativeIdentityInverse
  exact (actualGammaDeviationKernel_angularDiagonal parameters L rho alpha delta
    parameter epsilon field _).neg

/-- The correction produced by the actual gauge Neumann inverse is
angularly constant, even though it retains every cell frequency. -/
theorem actualGaugeCorrectionKernelOnBall_action_constant
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell 3) :
    IsAngularConstant parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualGaugeCorrectionKernelOnBall parameters L rho alpha delta parameter
          epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) input) := by
  unfold actualGaugeCorrectionKernelOnBall
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply constantMatrixKernel_action_constant
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply (actualNegativeGammaInverseKernelOnBall_angularDiagonal parameters L rho
    alpha delta parameter epsilon compactRadius field small compactNonnegative
    alphaSmall deltaSmall parameterSmall).action_constant
  unfold actualGaugeMeanRowsKernel
  rw [fullNegativeKernelAction_comp]
  exact angularMeanKernel_action_constant parameters angular cell _

end Grad.BoundaryKernelAction
