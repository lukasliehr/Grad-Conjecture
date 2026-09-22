import BCI2ExactBoundaryReference

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Grad.ActualBoundaryInverse

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Ledger

/-- Multiplication by the literal AD19 row minus its reference radial row. -/
def boundaryDeviationMultiplier (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low)
    (boundaryDeviationScalar_summable parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low)

/-- The ordinary angular derivative of the vanishing boundary deviation. -/
def boundaryRotatedDeviationMultiplier (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (fun component => angularCoefficientSequence
      (boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component))
    (fun component moment => (boundaryRotatedDeviationScalar_moment parameters L rho alpha delta parameter epsilon compact
      field compactNonnegative alphaSmall deltaSmall parameterSmall low component moment).1)

def boundaryDeviationMultiplierConstant (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, boundaryDeviationConstant parameters L compact component moment

theorem boundaryDeviationMultiplierConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    0 ≤ boundaryDeviationMultiplierConstant parameters L compact moment :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun component _ =>
    boundaryDeviationConstant_nonnegative parameters L compact component moment))

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

theorem boundaryDeviationMultiplier_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (moment : ℕ) :
    fullKernelMoment parameters moment
      (boundaryDeviationMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low) ≤
      boundaryDeviationMultiplierConstant parameters L compact moment *
        physicalBudget parameters field rho epsilon (moment + 5) :=
  rowMoment_bound parameters _ _ moment _ _ (fun component =>
    boundaryDeviationScalar_moment parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component moment)

theorem boundaryRotatedDeviationMultiplier_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (moment : ℕ) :
    fullKernelMoment parameters moment
      (boundaryRotatedDeviationMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low) ≤
      boundaryDeviationMultiplierConstant parameters L compact (moment + 1) *
        physicalBudget parameters field rho epsilon (moment + 6) :=
  rowMoment_bound parameters _ _ moment _ _ (fun component =>
    (boundaryRotatedDeviationScalar_moment parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component moment).2)

private theorem rowEntry_add (first second : Fin 3 → ℤ × ℤ → ℂ) (shift input : ℤ × ℤ) :
    rowMultiplicationEntry 3 (fun component mode => first component mode + second component mode) shift input =
      rowMultiplicationEntry 3 first shift input + rowMultiplicationEntry 3 second shift input := by
  unfold rowMultiplicationEntry
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro component _
  exact add_smul (first component shift) (second component shift) (matrixUnit (0 : Fin 1) component)

theorem boundaryReference_row (shift input : ℤ × ℤ) :
    rowMultiplicationEntry 3 boundaryReferenceScalar shift input =
      if shift = (0, 0) then matrixUnit (0 : Fin 1) (0 : Fin 3) else 0 := by
  have zeros (component : Fin 3) : (0 : ℂ) • matrixUnit (0 : Fin 1) component = 0 :=
    zero_smul ℂ (matrixUnit (0 : Fin 1) component)
  unfold rowMultiplicationEntry boundaryReferenceScalar
  by_cases zero : shift = (0, 0)
  · simp only [if_pos zero, ite_smul, one_smul, zeros]
    exact Finset.sum_ite_eq' Finset.univ 0 (fun component : Fin 3 => matrixUnit (0 : Fin 1) component)
  · simp only [if_neg zero, zeros, Finset.sum_const_zero]

theorem actualBoundaryMultiplier_decomposition (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    actualBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low =
      fullKernelAdd
        (boundaryDeviationMultiplier parameters L rho alpha delta parameter epsilon compact field
          compactNonnegative alphaSmall deltaSmall parameterSmall low)
        (coordinateProjectionKernel parameters 3 0) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  simp only [actualBoundaryMultiplier, boundaryDeviationMultiplier, boundaryRowMultiplicationKernel_entry,
    fullKernelAdd_entry, coordinateProjectionKernel, constantMatrixKernel_entry]
  rw [← boundaryReference_row shift input]
  have coefficients : boundaryScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low =
      (fun component mode => boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component mode + boundaryReferenceScalar component mode) := by
    funext component mode
    exact boundaryScalar_eq_deviation_add_reference parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component mode
  rw [coefficients, rowEntry_add]

theorem actualRotatedBoundaryMultiplier_decomposition (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    actualRotatedBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low =
      boundaryRotatedDeviationMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low := by
  unfold actualRotatedBoundaryMultiplier boundaryRotatedDeviationMultiplier
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  rw [boundaryRowMultiplicationKernel_entry, boundaryRowMultiplicationKernel_entry]
  exact congrArg (fun coefficient : Fin 3 → ℤ × ℤ → ℂ => rowMultiplicationEntry 3 coefficient shift input)
    (funext (fun component => angularBoundaryScalar_eq_deviation parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component))

end Grad.ActualBoundaryInverse
