import BKB39ActualEncodedFirstBounds

noncomputable section


set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

def actualEncodedFirstBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  fullKernelMoment parameters 0 (encodedD0InverseKernel parameters) *
    actualEncodedEBaseConstant parameters L compactRadius

theorem actualEncodedFirstBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualEncodedFirstBaseConstant parameters L compactRadius := by
  unfold actualEncodedFirstBaseConstant
  exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (actualEncodedEBaseConstant_nonnegative parameters L compactRadius)

/-- The single smaller B7 ball which simultaneously supplies the actual
gauge inverse and the encoded AE19 inverse. -/
def actualEncodedFirstLowRadius (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  min (actualGaugeInverseLowRadius parameters L compactRadius)
    (2 * (actualEncodedFirstBaseConstant parameters L compactRadius + 1))⁻¹

theorem actualEncodedFirstLowRadius_positive (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 < actualEncodedFirstLowRadius parameters L compactRadius := by
  unfold actualEncodedFirstLowRadius
  apply lt_min (actualGaugeInverseLowRadius_positive parameters L compactRadius)
  exact inv_pos.mpr (by
    linarith [actualEncodedFirstBaseConstant_nonnegative parameters L compactRadius])

theorem actualEncodedFirstLowRadius_le_gauge (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    actualEncodedFirstLowRadius parameters L compactRadius ≤
      actualGaugeInverseLowRadius parameters L compactRadius :=
  min_le_left _ _

theorem actualPreconditionedEncodedPerturbation_moment_zero_le_half
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
        (fullKernelNeg
          (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha
            delta parameter epsilon compactRadius field
              ((physicalBudget_monotone parameters field rho epsilon
                (by omega : 6 ≤ 7)).trans
                (small.trans (actualEncodedFirstLowRadius_le_gauge parameters L
                  compactRadius)))
              compactNonnegative alphaSmall deltaSmall parameterSmall)) ≤ 1 / 2 := by
  let constant := actualEncodedFirstBaseConstant parameters L compactRadius
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  have eBound := actualEncodedPerturbationKernel_moment_zero_le parameters L rho
    alpha delta parameter epsilon compactRadius field smallGauge compactNonnegative
    alphaSmall deltaSmall parameterSmall
  have preBound : fullKernelMoment parameters 0
      (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha delta
        parameter epsilon compactRadius field smallSix compactNonnegative alphaSmall
        deltaSmall parameterSmall) ≤
      constant * physicalBudget parameters field rho epsilon 7 := by
    unfold actualPreconditionedEncodedPerturbationKernel constant
    calc
      _ ≤ fullKernelMoment parameters 0 (encodedD0InverseKernel parameters) *
          fullKernelMoment parameters 0
            (actualEncodedPerturbationKernel parameters L rho alpha delta parameter
              epsilon compactRadius field smallSix compactNonnegative alphaSmall
              deltaSmall parameterSmall) :=
        fullKernelComposition_zero_moment_le _ _
      _ ≤ fullKernelMoment parameters 0 (encodedD0InverseKernel parameters) *
          (actualEncodedEBaseConstant parameters L compactRadius *
            physicalBudget parameters field rho epsilon 7) :=
        mul_le_mul_of_nonneg_left eBound
          (fullKernelMoment_nonnegative parameters 0 _)
      _ = _ := by unfold actualEncodedFirstBaseConstant; ring
  have budget : physicalBudget parameters field rho epsilon 7 ≤
      (2 * (constant + 1))⁻¹ := small.trans (min_le_right _ _)
  have total : fullKernelMoment parameters 0
      (actualPreconditionedEncodedPerturbationKernel parameters L rho alpha delta
        parameter epsilon compactRadius field smallSix compactNonnegative alphaSmall
        deltaSmall parameterSmall) ≤ constant * (2 * (constant + 1))⁻¹ :=
    preBound.trans (mul_le_mul_of_nonneg_left budget
      (actualEncodedFirstBaseConstant_nonnegative parameters L compactRadius))
  apply (fullKernelNeg_moment_le parameters 0 _).trans
  apply total.trans
  rw [← div_eq_mul_inv]
  have constantNonnegative : 0 ≤ constant :=
    actualEncodedFirstBaseConstant_nonnegative parameters L compactRadius
  apply (div_le_iff₀ (by linarith : 0 < 2 * (constant + 1))).mpr
  dsimp only [constant]
  nlinarith [actualEncodedFirstBaseConstant_nonnegative parameters L compactRadius]

/-- `(I+D0⁻¹ E)⁻¹`, constructed from the exact two-sided AE7 inverse. -/
def actualEncodedIdentityInverseKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let perturbation := actualPreconditionedEncodedPerturbationKernel parameters L rho
    alpha delta parameter epsilon compactRadius field smallSix compactNonnegative
    alphaSmall deltaSmall parameterSmall
  fullKernelNeg (fullKernelNegativeIdentityInverse parameters
    (fullKernelNeg perturbation) (1 / 2)
    (actualPreconditionedEncodedPerturbation_moment_zero_le_half parameters L rho
      alpha delta parameter epsilon compactRadius field small compactNonnegative
      alphaSmall deltaSmall parameterSmall) (by norm_num))

/-- AE24's actual first inverse `G_b=(I+D0⁻¹E)⁻¹D0⁻¹`. -/
def actualEncodedFirstInverseKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition
    (actualEncodedIdentityInverseKernel parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall)
    (encodedD0InverseKernel parameters)

end Grad.BoundaryKernelAction
