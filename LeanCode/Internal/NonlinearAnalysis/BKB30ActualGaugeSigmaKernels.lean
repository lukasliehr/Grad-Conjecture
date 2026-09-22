import BKB29ActualNeumannInverse
import GSP15OriginalGaugeSigmaConsumer

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation

def actualGaugeBoundaryCoefficients (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (mode : ℤ × ℤ) : ℂ :=
  gaugeScalar parameters L rho alpha delta parameter epsilon field low
    kind component 0 1 mode

theorem actualGaugeBoundaryCoefficients_moments (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
        epsilon field low kind component)) :=
  gaugeScalarMoment_summable parameters L rho alpha delta parameter epsilon
    field low kind component moment 0 1 zero_le_one le_rfl

def actualGaugeBoundaryKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (kind : Fin 2) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind)
    (actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low kind)

theorem actualGaugeBoundaryKernel_entry_apply (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (kind : Fin 2)
    (shift input : ℤ × ℤ) (value : ComplexEuclidean 3) :
    (actualGaugeBoundaryKernel parameters L rho alpha delta parameter epsilon
      field low kind).entry shift input value =
      (∑ component : Fin 3,
        gaugeScalar parameters L rho alpha delta parameter epsilon field low
          kind component 0 1 shift * value component) •
        Grad.GaugeCoefficients.Physical.Ledger.operatorBasis (0 : Fin 1) :=
  boundaryRowMultiplicationKernel_entry_apply parameters 3
    (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind)
    (actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low kind) shift input value

theorem actualGaugeBoundaryKernel_moment_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (kind : Fin 2)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualGaugeBoundaryKernel parameters L rho alpha delta parameter
          epsilon field low kind) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin 3,
          gaugeScalarConstant parameters L compactRadius kind component moment 0 *
            physicalBudget parameters field rho epsilon (moment + 5) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind)
    (actualGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low kind)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro component _
  exact gaugeScalarMoment_bound parameters L rho alpha delta parameter epsilon
    field low compactRadius kind component moment 0 1 zero_le_one le_rfl
      compactNonnegative alphaSmall deltaSmall parameterSmall

def actualRotatedGaugeBoundaryCoefficients (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) : ℤ × ℤ → ℂ :=
  angularCoefficientSequence
    (actualGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind component)

theorem actualRotatedGaugeBoundaryCoefficients_moments
    (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualRotatedGaugeBoundaryCoefficients parameters L rho alpha delta
        parameter epsilon field low kind component)) :=
  angularCoefficientSequence_moment_summable parameters moment 1 _
    (gaugeScalarMoment_summable parameters L rho alpha delta parameter epsilon
      field low kind component (moment + 1) 0 1 zero_le_one le_rfl)

def actualRotatedGaugeBoundaryKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (kind : Fin 2) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualRotatedGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind)
    (actualRotatedGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low kind)

theorem actualRotatedGaugeBoundaryKernel_moment_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (kind : Fin 2)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualRotatedGaugeBoundaryKernel parameters L rho alpha delta parameter
          epsilon field low kind) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin 3,
          gaugeScalarConstant parameters L compactRadius kind component
              (moment + 1) 0 *
            physicalBudget parameters field rho epsilon (moment + 6) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualRotatedGaugeBoundaryCoefficients parameters L rho alpha delta parameter
      epsilon field low kind)
    (actualRotatedGaugeBoundaryCoefficients_moments parameters L rho alpha delta
      parameter epsilon field low kind)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro component _
  exact (gaugeAngularScalarMoment_bound parameters L rho alpha delta parameter
    epsilon field low compactRadius kind component moment 0 1 zero_le_one le_rfl
      compactNonnegative alphaSmall deltaSmall parameterSmall).2

def actualSigmaBoundaryCoefficients (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (mode : ℤ × ℤ) : ℂ :=
  sigmaScalar parameters L rho epsilon field low component 0 1 mode

theorem actualSigmaBoundaryCoefficients_moments (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualSigmaBoundaryCoefficients parameters L rho epsilon field low
        component)) :=
  sigmaScalarMoment_summable parameters L rho epsilon field low component
    moment 0 1 zero_le_one le_rfl

def actualSigmaBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualSigmaBoundaryCoefficients parameters L rho epsilon field low)
    (actualSigmaBoundaryCoefficients_moments parameters L rho epsilon field low)

theorem actualSigmaBoundaryKernel_moment_le (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualSigmaBoundaryKernel parameters L rho epsilon field low) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin 3,
          sigmaScalarConstant parameters L component moment 0 *
            physicalBudget parameters field rho epsilon (moment + 5) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualSigmaBoundaryCoefficients parameters L rho epsilon field low)
    (actualSigmaBoundaryCoefficients_moments parameters L rho epsilon field low)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro component _
  exact sigmaScalarMoment_bound parameters L rho epsilon field low component
    moment 0 1 zero_le_one le_rfl

def actualRotatedSigmaBoundaryCoefficients (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) : ℤ × ℤ → ℂ :=
  angularCoefficientSequence
    (actualSigmaBoundaryCoefficients parameters L rho epsilon field low component)

theorem actualRotatedSigmaBoundaryCoefficients_moments
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualRotatedSigmaBoundaryCoefficients parameters L rho epsilon field low
        component)) :=
  angularCoefficientSequence_moment_summable parameters moment 1 _
    (sigmaScalarMoment_summable parameters L rho epsilon field low component
      (moment + 1) 0 1 zero_le_one le_rfl)

def actualRotatedSigmaBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualRotatedSigmaBoundaryCoefficients parameters L rho epsilon field low)
    (actualRotatedSigmaBoundaryCoefficients_moments parameters L rho epsilon field low)

theorem actualRotatedSigmaBoundaryKernel_moment_le
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field low) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin 3,
          sigmaScalarConstant parameters L component (moment + 1) 0 *
            physicalBudget parameters field rho epsilon (moment + 6) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualRotatedSigmaBoundaryCoefficients parameters L rho epsilon field low)
    (actualRotatedSigmaBoundaryCoefficients_moments parameters L rho epsilon field low)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro component _
  exact (sigmaAngularScalarMoment_bound parameters L rho epsilon field low component
    moment 0 1 zero_le_one le_rfl).2

end Grad.BoundaryKernelAction
