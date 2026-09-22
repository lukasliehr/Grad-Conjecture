import BKB34EncodedCoordinateKernels

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

def actualGaugeRowsCoefficients (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (row : Fin 2) (column : Fin 3) : ℤ × ℤ → ℂ :=
  actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
    epsilon field low row column

theorem actualGaugeRowsCoefficients_moments (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (row : Fin 2) (column : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualGaugeRowsCoefficients parameters L rho alpha delta parameter
        epsilon field low row column)) :=
  actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
    parameter epsilon field low row column moment

def actualGaugeRowsKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 2 :=
  boundaryMatrixMultiplicationKernel parameters 3 2
    (actualGaugeRowsCoefficients parameters L rho alpha delta parameter
      epsilon field low)
    (actualGaugeRowsCoefficients_moments parameters L rho alpha delta parameter
      epsilon field low)

def actualGaugeMeanRowsKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 2 :=
  fullKernelComposition (angularMeanKernel parameters 2)
    (actualGaugeRowsKernel parameters L rho alpha delta parameter epsilon field low)

def actualGammaDeviationCoefficients (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (row column : Fin 2) (shift : ℤ × ℤ) : ℂ :=
  if shift.1 = 0 then
    actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low row column.succ shift
  else 0

theorem actualGammaDeviationCoefficients_moments
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (row column : Fin 2) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualGammaDeviationCoefficients parameters L rho alpha delta parameter
        epsilon field low row column)) := by
  apply Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (fun shift => ?_)
    (actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low row column.succ moment)
  by_cases zero : shift.1 = 0
  · unfold actualGammaDeviationCoefficients
    unfold productMoment
    dsimp only
    rw [if_pos zero]
  · unfold actualGammaDeviationCoefficients
    unfold productMoment
    dsimp only
    rw [if_neg zero]
    simp only [norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le
        (pow_nonneg (annularFrequency_nonnegative _ _) _)) (norm_nonneg _)

/-- The exact `Gamma-I` kernel: retain only angular displacement zero in
the last two columns of the two physical gauge-deviation rows. -/
def actualGammaDeviationKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 2 2 :=
  boundaryMatrixMultiplicationKernel parameters 2 2
    (actualGammaDeviationCoefficients parameters L rho alpha delta parameter
      epsilon field low)
    (actualGammaDeviationCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low)

theorem actualGammaDeviationKernel_moment_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualGammaDeviationKernel parameters L rho alpha delta parameter
          epsilon field low) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin 2, ∑ column : Fin 2,
          gaugeScalarConstant parameters L compactRadius row column.succ moment 0 *
            physicalBudget parameters field rho epsilon (moment + 5) := by
  apply (boundaryMatrixMultiplicationKernel_moment_le parameters 2 2 moment
    (actualGammaDeviationCoefficients parameters L rho alpha delta parameter
      epsilon field low)
    (actualGammaDeviationCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro row _
  apply Finset.sum_le_sum
  intro column _
  have domination (shift : ℤ × ℤ) :
      productMoment parameters moment 1
          (actualGammaDeviationCoefficients parameters L rho alpha delta parameter
            epsilon field low row column) shift ≤
        productMoment parameters moment 1
          (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
            epsilon field low row column.succ) shift := by
    by_cases zero : shift.1 = 0
    · unfold actualGammaDeviationCoefficients
      unfold productMoment
      dsimp only
      rw [if_pos zero]
    · unfold actualGammaDeviationCoefficients
      unfold productMoment
      dsimp only
      rw [if_neg zero]
      simp only [norm_zero, mul_zero]
      exact mul_nonneg
        (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le
          (pow_nonneg (annularFrequency_nonnegative _ _) _)) (norm_nonneg _)
  calc
    _ ≤ ∑' shift, productMoment parameters moment 1
        (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
          epsilon field low row column.succ) shift :=
      (actualGammaDeviationCoefficients_moments parameters L rho alpha delta
        parameter epsilon field low row column moment).tsum_le_tsum domination
          (actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
            parameter epsilon field low row column.succ moment)
    _ ≤ _ := gaugeScalarMoment_bound parameters L rho alpha delta parameter epsilon
      field low compactRadius row column.succ moment 0 1 zero_le_one le_rfl
        compactNonnegative alphaSmall deltaSmall parameterSmall

/-- The kernel of `-Gamma⁻¹`, obtained from the exact two-sided Neumann
inverse of `-(I+(Gamma-I))`. -/
def actualNegativeGammaInverseKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (inverseRadius : ℝ)
    (inverseBound : fullKernelMoment parameters 0
      (fullKernelNeg (actualGammaDeviationKernel parameters L rho alpha delta
        parameter epsilon field low)) ≤ inverseRadius)
    (inverseSmall : inverseRadius < 1) :
    FullTwoFrequencyKernel parameters 2 2 :=
  fullKernelNegativeIdentityInverse parameters
    (fullKernelNeg (actualGammaDeviationKernel parameters L rho alpha delta
      parameter epsilon field low)) inverseRadius inverseBound inverseSmall

def actualGaugeCorrectionKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (inverseRadius : ℝ)
    (inverseBound : fullKernelMoment parameters 0
      (fullKernelNeg (actualGammaDeviationKernel parameters L rho alpha delta
        parameter epsilon field low)) ≤ inverseRadius)
    (inverseSmall : inverseRadius < 1) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (tailInjectionKernel parameters)
    (fullKernelComposition
      (actualNegativeGammaInverseKernel parameters L rho alpha delta parameter
        epsilon field low inverseRadius inverseBound inverseSmall)
      (actualGaugeMeanRowsKernel parameters L rho alpha delta parameter epsilon
        field low))

def actualGaugeQKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (inverseRadius : ℝ)
    (inverseBound : fullKernelMoment parameters 0
      (fullKernelNeg (actualGammaDeviationKernel parameters L rho alpha delta
        parameter epsilon field low)) ≤ inverseRadius)
    (inverseSmall : inverseRadius < 1) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd (fullIdentityKernel parameters 3)
    (actualGaugeCorrectionKernel parameters L rho alpha delta parameter epsilon
      field low inverseRadius inverseBound inverseSmall)

end Grad.BoundaryKernelAction
