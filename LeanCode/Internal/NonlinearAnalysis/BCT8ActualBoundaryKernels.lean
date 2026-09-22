import BCT7GenuineBoundaryRotation
import BKB25RowMultiplicationKernel

noncomputable section
open scoped BigOperators

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- Actual multiplication by the complete AD19 boundary covector. -/
def actualBoundaryMultiplier (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (boundaryScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low)
    (boundaryScalarMoment_summable parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low)

/-- Multiplication by the genuine ordinary angular derivative of that
physical covector, identified by BCT7. -/
def actualRotatedBoundaryMultiplier (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (fun component => angularCoefficientSequence
      (boundaryScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component))
    (fun component moment => (boundaryRotatedScalarMoment_bound parameters L rho alpha delta parameter epsilon compact
      field compactNonnegative alphaSmall deltaSmall parameterSmall low component moment).1)

def boundaryMultiplierConstant (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, boundaryScalarConstant parameters L compact component moment

theorem boundaryMultiplierConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    0 ≤ boundaryMultiplierConstant parameters L compact moment :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun component _ =>
    boundaryScalarConstant_nonnegative parameters L compact component moment))

private theorem rowMoment_bound (parameters : PhaseParameters)
    (coefficient : Fin 3 → ℤ × ℤ → ℂ)
    (moments : ∀ component moment, Summable (productMoment parameters moment 1 (coefficient component)))
    (moment : ℕ) (constants : Fin 3 → ℝ) (budget : ℝ)
    (bound : ∀ component, (∑' mode, productMoment parameters moment 1 (coefficient component) mode) ≤
      constants component * budget) :
    fullKernelMoment parameters moment (boundaryRowMultiplicationKernel parameters 3 coefficient moments) ≤
      (Real.exp (parameters.sigma0 + parameters.gamma) * ∑ component, constants component) * budget := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment coefficient moments).trans
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun component _ => bound component)
  rw [← Finset.sum_mul] at summed
  exact (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm

theorem actualBoundaryMultiplier_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (moment : ℕ) :
    fullKernelMoment parameters moment
      (actualBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low) ≤
      boundaryMultiplierConstant parameters L compact moment *
        (1 + physicalBudget parameters field rho epsilon (moment + 5)) :=
  rowMoment_bound parameters _ _ moment _ _ (fun component =>
    boundaryScalarMoment_bound parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component moment)

theorem actualRotatedBoundaryMultiplier_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (moment : ℕ) :
    fullKernelMoment parameters moment
      (actualRotatedBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low) ≤
      boundaryMultiplierConstant parameters L compact (moment + 1) *
        (1 + physicalBudget parameters field rho epsilon (moment + 6)) :=
  rowMoment_bound parameters _ _ moment _ _ (fun component =>
    (boundaryRotatedScalarMoment_bound parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component moment).2)

end Grad.ActualBoundaryPrimitives
