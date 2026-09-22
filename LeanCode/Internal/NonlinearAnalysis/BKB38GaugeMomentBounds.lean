import BKB37ActualEncodedFirstSystem

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

def actualGaugeRowsBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 3,
      gaugeScalarConstant parameters L compactRadius row column 0 0

theorem actualGaugeRowsBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualGaugeRowsBaseConstant parameters L compactRadius := by
  unfold actualGaugeRowsBaseConstant
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun row _ => Finset.sum_nonneg fun column _ =>
      gaugeScalarConstant_nonnegative parameters L compactRadius row column 0 0)

theorem actualGaugeRowsKernel_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualGaugeRowsKernel parameters L rho alpha delta parameter epsilon field low) ≤
      actualGaugeRowsBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 5 := by
  apply (boundaryMatrixMultiplicationKernel_moment_le parameters 3 2 0
    (actualGaugeRowsCoefficients parameters L rho alpha delta parameter epsilon
      field low)
    (actualGaugeRowsCoefficients_moments parameters L rho alpha delta parameter
      epsilon field low)).trans
  have each (row : Fin 2) (column : Fin 3) :=
    gaugeScalarMoment_bound parameters L rho alpha delta parameter epsilon field low
      compactRadius row column 0 0 1 zero_le_one le_rfl compactNonnegative
      alphaSmall deltaSmall parameterSmall
  calc
    Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin 2, ∑ column : Fin 3,
          ∑' shift, productMoment parameters 0 1
            (actualGaugeRowsCoefficients parameters L rho alpha delta parameter
              epsilon field low row column) shift ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin 2, ∑ column : Fin 3,
          gaugeScalarConstant parameters L compactRadius row column 0 0 *
            physicalBudget parameters field rho epsilon 5 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum
      intro row _
      apply Finset.sum_le_sum
      intro column _
      exact each row column
    _ = actualGaugeRowsBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 5 := by
      unfold actualGaugeRowsBaseConstant
      rw [mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_mul]

def actualNegativeGammaInverseBaseConstant (parameters : PhaseParameters) : ℝ :=
  fullKernelMoment parameters 0 (fullIdentityKernel parameters 2) +
    fullKernelNeumannConstant 0 (1 / 2) * (1 / 2)

theorem actualNegativeGammaInverseBaseConstant_nonnegative
    (parameters : PhaseParameters) :
    0 ≤ actualNegativeGammaInverseBaseConstant parameters := by
  unfold actualNegativeGammaInverseBaseConstant fullKernelNeumannConstant
  exact add_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (mul_nonneg
      (tsum_nonneg fun exponent => mul_nonneg
        (pow_nonneg (by positivity) _) (pow_nonneg (by norm_num) _))
      (by norm_num))

theorem actualNegativeGammaInverseKernelOnBall_moment_zero_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
      (actualNegativeGammaInverseKernelOnBall parameters L rho alpha delta
        parameter epsilon compactRadius field small compactNonnegative alphaSmall
        deltaSmall parameterSmall) ≤
      actualNegativeGammaInverseBaseConstant parameters := by
  unfold actualNegativeGammaInverseKernelOnBall actualNegativeGammaInverseKernel
  have bound := fullKernelNegativeIdentityInverse_moment_le parameters 0
    (fullKernelNeg
      (actualGammaDeviationKernel parameters L rho alpha delta parameter epsilon
        field (small.trans (actualGaugeInverseLowRadius_le_original parameters L
          compactRadius)))) (1 / 2)
    (actualGammaInverseRadius_bound parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (by norm_num)
  apply bound.trans
  unfold actualNegativeGammaInverseBaseConstant
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (actualGammaInverseRadius_bound parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (by
      unfold fullKernelNeumannConstant
      exact tsum_nonneg fun exponent => mul_nonneg
        (pow_nonneg (by positivity) _) (pow_nonneg (by norm_num) _))

def actualGaugeQBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  fullKernelMoment parameters 0 (fullIdentityKernel parameters 3) +
    fullKernelMoment parameters 0 (tailInjectionKernel parameters) *
      (actualNegativeGammaInverseBaseConstant parameters *
        (fullKernelMoment parameters 0 (angularMeanKernel parameters 2) *
          actualGaugeRowsBaseConstant parameters L compactRadius))

theorem actualGaugeQBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualGaugeQBaseConstant parameters L compactRadius := by
  unfold actualGaugeQBaseConstant
  exact add_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (actualNegativeGammaInverseBaseConstant_nonnegative parameters)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (actualGaugeRowsBaseConstant_nonnegative parameters L compactRadius))))

theorem actualGaugeQKernelOnBall_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤
      actualGaugeQBaseConstant parameters L compactRadius := by
  have coefficientLow := small.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  have budgetFive : physicalBudget parameters field rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters field rho epsilon (by omega : 5 ≤ 6)).trans
      (small.trans ((actualGaugeInverseLowRadius_le_original parameters L
        compactRadius).trans (min_le_left _ _)))
  have rows : fullKernelMoment parameters 0
      (actualGaugeRowsKernel parameters L rho alpha delta parameter epsilon field
        coefficientLow) ≤ actualGaugeRowsBaseConstant parameters L compactRadius :=
    (actualGaugeRowsKernel_moment_zero_le parameters L rho alpha delta parameter
      epsilon compactRadius field coefficientLow compactNonnegative alphaSmall
      deltaSmall parameterSmall).trans
        ((mul_le_mul_of_nonneg_left budgetFive
          (actualGaugeRowsBaseConstant_nonnegative parameters L compactRadius)).trans_eq
            (mul_one _))
  have meanRows : fullKernelMoment parameters 0
      (actualGaugeMeanRowsKernel parameters L rho alpha delta parameter epsilon field
        coefficientLow) ≤
      fullKernelMoment parameters 0 (angularMeanKernel parameters 2) *
        actualGaugeRowsBaseConstant parameters L compactRadius :=
    (fullKernelComposition_zero_moment_le
      (angularMeanKernel parameters 2)
      (actualGaugeRowsKernel parameters L rho alpha delta parameter epsilon field
        coefficientLow)).trans
      (mul_le_mul_of_nonneg_left rows
        (fullKernelMoment_nonnegative parameters 0 _))
  have inverse := actualNegativeGammaInverseKernelOnBall_moment_zero_le parameters
    L rho alpha delta parameter epsilon compactRadius field small compactNonnegative
    alphaSmall deltaSmall parameterSmall
  have nested : fullKernelMoment parameters 0
      (fullKernelComposition
        (actualNegativeGammaInverseKernelOnBall parameters L rho alpha delta
          parameter epsilon compactRadius field small compactNonnegative alphaSmall
          deltaSmall parameterSmall)
        (actualGaugeMeanRowsKernel parameters L rho alpha delta parameter epsilon field
          coefficientLow)) ≤
      actualNegativeGammaInverseBaseConstant parameters *
        (fullKernelMoment parameters 0 (angularMeanKernel parameters 2) *
          actualGaugeRowsBaseConstant parameters L compactRadius) :=
    (fullKernelComposition_zero_moment_le _ _).trans
      (mul_le_mul inverse meanRows (fullKernelMoment_nonnegative parameters 0 _)
        (actualNegativeGammaInverseBaseConstant_nonnegative parameters))
  have correction : fullKernelMoment parameters 0
      (actualGaugeCorrectionKernelOnBall parameters L rho alpha delta parameter
        epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      fullKernelMoment parameters 0 (tailInjectionKernel parameters) *
        (actualNegativeGammaInverseBaseConstant parameters *
          (fullKernelMoment parameters 0 (angularMeanKernel parameters 2) *
            actualGaugeRowsBaseConstant parameters L compactRadius)) :=
    (fullKernelComposition_zero_moment_le _ _).trans
      (mul_le_mul_of_nonneg_left nested (fullKernelMoment_nonnegative parameters 0 _))
  unfold actualGaugeQKernelOnBall actualGaugeQBaseConstant
  exact (fullKernelAdd_moment_le parameters 0 _ _).trans (add_le_add le_rfl correction)

end Grad.BoundaryKernelAction
