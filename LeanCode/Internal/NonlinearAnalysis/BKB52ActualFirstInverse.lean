import BKB51PositiveIdentityInverse

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

theorem actualEncodedIdentityInverseKernel_right (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    let smallGauge := small.trans
      (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
    let smallSix := (physicalBudget_monotone parameters field rho epsilon
      (by omega : 6 ≤ 7)).trans smallGauge
    let perturbation := actualPreconditionedEncodedPerturbationKernel parameters L rho
      alpha delta parameter epsilon compactRadius field smallSix compactNonnegative
      alphaSmall deltaSmall parameterSmall
    fullKernelComposition
        (fullKernelAdd (fullIdentityKernel parameters 3) perturbation)
        (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter
          epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) =
      fullIdentityKernel parameters 3 := by
  dsimp only
  unfold actualEncodedIdentityInverseKernel
  exact fullKernelPositiveIdentityInverse_right parameters _ (1 / 2)
    (actualPreconditionedEncodedPerturbation_moment_zero_le_half parameters L rho
      alpha delta parameter epsilon compactRadius field small compactNonnegative
      alphaSmall deltaSmall parameterSmall) (by norm_num)

theorem actualEncodedIdentityInverseKernel_left (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    let smallGauge := small.trans
      (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
    let smallSix := (physicalBudget_monotone parameters field rho epsilon
      (by omega : 6 ≤ 7)).trans smallGauge
    let perturbation := actualPreconditionedEncodedPerturbationKernel parameters L rho
      alpha delta parameter epsilon compactRadius field smallSix compactNonnegative
      alphaSmall deltaSmall parameterSmall
    fullKernelComposition
        (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter
          epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall)
        (fullKernelAdd (fullIdentityKernel parameters 3) perturbation) =
      fullIdentityKernel parameters 3 := by
  dsimp only
  unfold actualEncodedIdentityInverseKernel
  exact fullKernelPositiveIdentityInverse_left parameters _ (1 / 2)
    (actualPreconditionedEncodedPerturbation_moment_zero_le_half parameters L rho
      alpha delta parameter epsilon compactRadius field small compactNonnegative
      alphaSmall deltaSmall parameterSmall) (by norm_num)

/-- AE17's actual first encoded operator `D0+E`. -/
def actualEncodedFirstSystemKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd (encodedD0Kernel parameters)
    (actualEncodedPerturbationKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)

theorem actualEncodedFirstSystemKernel_factor (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    actualEncodedFirstSystemKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall =
      fullKernelComposition (encodedD0Kernel parameters)
        (fullKernelAdd (fullIdentityKernel parameters 3)
          (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha delta
            parameter epsilon compactRadius field small compactNonnegative alphaSmall
            deltaSmall parameterSmall)) := by
  unfold actualEncodedFirstSystemKernel actualPreconditionedEncodedPerturbationKernel
  rw [fullKernelComposition_add_inner, fullKernel_comp_identity,
    ← fullKernelComposition_assoc, encodedD0Kernel_inverse_right,
    fullIdentityKernel_comp]

/-- AE24: the constructed first inverse is genuinely a right inverse of `D0+E`. -/
theorem actualEncodedFirstInverseKernel_right (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    let smallGauge := small.trans
      (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
    let smallSix := (physicalBudget_monotone parameters field rho epsilon
      (by omega : 6 ≤ 7)).trans smallGauge
    fullKernelComposition
        (actualEncodedFirstSystemKernel parameters L rho alpha delta parameter epsilon
          compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
        (actualEncodedFirstInverseKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) =
      fullIdentityKernel parameters 3 := by
  dsimp only
  rw [actualEncodedFirstSystemKernel_factor]
  unfold actualEncodedFirstInverseKernel
  rw [fullKernelComposition_assoc,
    ← fullKernelComposition_assoc
      (fullKernelAdd (fullIdentityKernel parameters 3)
        (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha delta
          parameter epsilon compactRadius field _ compactNonnegative alphaSmall
          deltaSmall parameterSmall))
      (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter
        epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall)
      (encodedD0InverseKernel parameters),
    actualEncodedIdentityInverseKernel_right,
    fullIdentityKernel_comp, encodedD0Kernel_inverse_right]

end Grad.BoundaryKernelAction
