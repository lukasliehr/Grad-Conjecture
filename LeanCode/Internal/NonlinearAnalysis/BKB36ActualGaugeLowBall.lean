import BKB35ActualGaugeCorrection

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

/-- The fixed compact-parameter constant controlling the zero-th moment of
`Gamma-I`.  It is chosen before the physical state. -/
def actualGammaBaseConstant (parameters : PhaseParameters) (L compactRadius : ℝ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 2,
      gaugeScalarConstant parameters L compactRadius row column.succ 0 0

theorem actualGammaBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualGammaBaseConstant parameters L compactRadius := by
  unfold actualGammaBaseConstant
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun row _ => Finset.sum_nonneg fun column _ =>
      gaugeScalarConstant_nonnegative parameters L compactRadius row column.succ 0 0)

/-- One actual physical low ball, fixed before all higher grades, on which the
last-two-coordinate gauge matrix is invertible by its exact Neumann series. -/
def actualGaugeInverseLowRadius (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  min (originalCoefficientLowRadius parameters L)
    (2 * (actualGammaBaseConstant parameters L compactRadius + 1))⁻¹

theorem actualGaugeInverseLowRadius_positive (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 < actualGaugeInverseLowRadius parameters L compactRadius := by
  unfold actualGaugeInverseLowRadius
  apply lt_min (originalCoefficientLowRadius_positive parameters L)
  exact inv_pos.mpr (by
    linarith [actualGammaBaseConstant_nonnegative parameters L compactRadius])

theorem actualGaugeInverseLowRadius_le_original (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    actualGaugeInverseLowRadius parameters L compactRadius ≤
      originalCoefficientLowRadius parameters L :=
  min_le_left _ _

theorem actualGammaDeviationKernel_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualGammaDeviationKernel parameters L rho alpha delta parameter
          epsilon field
            (small.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius))) ≤
      actualGammaBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 5 := by
  have bound := actualGammaDeviationKernel_moment_le parameters L rho alpha delta
    parameter epsilon compactRadius field
      (small.trans (actualGaugeInverseLowRadius_le_original parameters L compactRadius))
      compactNonnegative alphaSmall deltaSmall parameterSmall 0
  calc
    _ ≤ Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin 2, ∑ column : Fin 2,
          gaugeScalarConstant parameters L compactRadius row column.succ 0 0 *
            physicalBudget parameters field rho epsilon (0 + 5) := bound
    _ = actualGammaBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 5 := by
      unfold actualGammaBaseConstant
      simp only [zero_add]
      rw [mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_mul]

theorem actualGammaInverseRadius_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (fullKernelNeg
          (actualGammaDeviationKernel parameters L rho alpha delta parameter
            epsilon field
              (small.trans (actualGaugeInverseLowRadius_le_original parameters L
                compactRadius)))) ≤ 1 / 2 := by
  let constant := actualGammaBaseConstant parameters L compactRadius
  have constantNonnegative : 0 ≤ constant :=
    actualGammaBaseConstant_nonnegative parameters L compactRadius
  have budgetFive : physicalBudget parameters field rho epsilon 5 ≤
      (2 * (constant + 1))⁻¹ :=
    (physicalBudget_monotone parameters field rho epsilon (by omega : 5 ≤ 6)).trans
      (small.trans (min_le_right _ _))
  have deviationBound : fullKernelMoment parameters 0
      (actualGammaDeviationKernel parameters L rho alpha delta parameter epsilon
        field (small.trans (actualGaugeInverseLowRadius_le_original parameters L
          compactRadius))) ≤ constant * (2 * (constant + 1))⁻¹ :=
    (actualGammaDeviationKernel_moment_zero_le parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall).trans
        (mul_le_mul_of_nonneg_left budgetFive constantNonnegative)
  apply (fullKernelNeg_moment_le parameters 0 _).trans
  apply deviationBound.trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (constant + 1))).mpr
  nlinarith

/-- The actual kernel of `-Gamma⁻¹` with all analytic hypotheses discharged
from the single physical low-ball condition. -/
def actualNegativeGammaInverseKernelOnBall (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 2 2 :=
  actualNegativeGammaInverseKernel parameters L rho alpha delta parameter epsilon
    field (small.trans (actualGaugeInverseLowRadius_le_original parameters L
      compactRadius))
    (1 / 2)
    (actualGammaInverseRadius_bound parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (by norm_num)

/-- The exact actual gauge correction `C = tail ∘ (-Gamma⁻¹) ∘ Pi delta-ell`. -/
def actualGaugeCorrectionKernelOnBall (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (tailInjectionKernel parameters)
    (fullKernelComposition
      (actualNegativeGammaInverseKernelOnBall parameters L rho alpha delta parameter
        epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall)
      (actualGaugeMeanRowsKernel parameters L rho alpha delta parameter epsilon field
        (small.trans (actualGaugeInverseLowRadius_le_original parameters L
          compactRadius))))

/-- The exact actual gauge projection `Q = I+C`, depending only on the original
physical state and the one fixed low-ball proof. -/
def actualGaugeQKernelOnBall (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd (fullIdentityKernel parameters 3)
    (actualGaugeCorrectionKernelOnBall parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall)

end Grad.BoundaryKernelAction
