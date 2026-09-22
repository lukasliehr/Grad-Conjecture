import BKB42ActualMassSystem

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

def actualEncodedIdentityInverseBaseConstant (parameters : PhaseParameters) : ℝ :=
  fullKernelMoment parameters 0 (fullIdentityKernel parameters 3) +
    fullKernelNeumannConstant 0 (1 / 2) * (1 / 2)

theorem actualEncodedIdentityInverseBaseConstant_nonnegative
    (parameters : PhaseParameters) :
    0 ≤ actualEncodedIdentityInverseBaseConstant parameters := by
  unfold actualEncodedIdentityInverseBaseConstant fullKernelNeumannConstant
  exact add_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (mul_nonneg
      (tsum_nonneg fun exponent => mul_nonneg
        (pow_nonneg (by positivity) _) (pow_nonneg (by norm_num) _))
      (by norm_num))

theorem actualEncodedIdentityInverseKernel_moment_zero_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter
          epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤
      actualEncodedIdentityInverseBaseConstant parameters := by
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let perturbation := actualPreconditionedEncodedPerturbationKernel parameters L rho
    alpha delta parameter epsilon compactRadius field smallSix compactNonnegative
    alphaSmall deltaSmall parameterSmall
  have perturbationBound :=
    actualPreconditionedEncodedPerturbation_moment_zero_le_half parameters L rho
      alpha delta parameter epsilon compactRadius field small compactNonnegative
      alphaSmall deltaSmall parameterSmall
  unfold actualEncodedIdentityInverseKernel
  dsimp only
  apply (fullKernelNeg_moment_le parameters 0 _).trans
  apply (fullKernelNegativeIdentityInverse_moment_le parameters 0
    (fullKernelNeg perturbation) (1 / 2) perturbationBound (by norm_num)).trans
  unfold actualEncodedIdentityInverseBaseConstant
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left perturbationBound
    (by
      unfold fullKernelNeumannConstant
      exact tsum_nonneg fun exponent => mul_nonneg
        (pow_nonneg (by positivity) _) (pow_nonneg (by norm_num) _)))

def actualEncodedFirstInverseBaseConstant (parameters : PhaseParameters) : ℝ :=
  actualEncodedIdentityInverseBaseConstant parameters *
    fullKernelMoment parameters 0 (encodedD0InverseKernel parameters)

theorem actualEncodedFirstInverseBaseConstant_nonnegative
    (parameters : PhaseParameters) :
    0 ≤ actualEncodedFirstInverseBaseConstant parameters :=
  mul_nonneg (actualEncodedIdentityInverseBaseConstant_nonnegative parameters)
    (fullKernelMoment_nonnegative parameters 0 _)

theorem actualEncodedFirstInverseKernel_moment_zero_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualEncodedFirstInverseKernel parameters L rho alpha delta parameter
          epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤
      actualEncodedFirstInverseBaseConstant parameters := by
  unfold actualEncodedFirstInverseKernel actualEncodedFirstInverseBaseConstant
  exact fullKernelComposition_zero_moment_le_of _ _ _ _
    (actualEncodedIdentityInverseKernel_moment_zero_le parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall) le_rfl
    (actualEncodedIdentityInverseBaseConstant_nonnegative parameters)
    (fullKernelMoment_nonnegative parameters 0 _)

def actualUnknownQABaseConstant (parameters : PhaseParameters) : ℝ :=
  fullKernelMoment parameters 0 (actualUnknownQAKernel parameters)

def actualGaugeUnknownQABaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  actualGaugeQBaseConstant parameters L compactRadius *
    actualUnknownQABaseConstant parameters

theorem actualGaugeUnknownQABaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualGaugeUnknownQABaseConstant parameters L compactRadius := by
  unfold actualGaugeUnknownQABaseConstant actualUnknownQABaseConstant
  exact mul_nonneg (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
    (fullKernelMoment_nonnegative parameters 0 _)

theorem actualGaugeUnknownQAKernel_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (fullKernelComposition
          (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
            compactRadius field
              ((physicalBudget_monotone parameters field rho epsilon
                (by omega : 6 ≤ 7)).trans
                (small.trans (actualEncodedFirstLowRadius_le_gauge parameters L
                  compactRadius)))
              compactNonnegative alphaSmall deltaSmall parameterSmall)
          (actualUnknownQAKernel parameters)) ≤
      actualGaugeUnknownQABaseConstant parameters L compactRadius := by
  exact fullKernelComposition_zero_moment_le_of _ _ _ _
    (actualGaugeQKernelOnBall_moment_zero_le parameters L rho alpha delta parameter
      epsilon compactRadius field
        ((physicalBudget_monotone parameters field rho epsilon
          (by omega : 6 ≤ 7)).trans
          (small.trans (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)))
        compactNonnegative alphaSmall deltaSmall parameterSmall)
    le_rfl (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
    (fullKernelMoment_nonnegative parameters 0 _)

end Grad.BoundaryKernelAction
