import BCI11VanishingMomentAllocation

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.ActualBoundaryInverse
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives

theorem actualSigmaBoundaryKernel_vanishingMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    BoundaryDeviationMoments parameters L compactRadius
      (fun state => actualSigmaBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  have estimated := actualSigmaBoundaryKernel_moment_le parameters L state.val.rho state.val.epsilon
    state.val.field state.val.coefficientSmall moment
  have factored : fullKernelMoment parameters moment
      (actualSigmaBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall) ≤
      constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 5) := by
    simpa only [constant, Finset.sum_mul, mul_assoc] using estimated
  exact factored.trans (mul_le_mul (le_abs_self constant)
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment + 5 ≤ moment + 7))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant))

theorem actualRotatedSigmaBoundaryKernel_vanishingMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    BoundaryDeviationMoments parameters L compactRadius
      (fun state => actualRotatedSigmaBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  have estimated := actualRotatedSigmaBoundaryKernel_moment_le parameters L state.val.rho state.val.epsilon
    state.val.field state.val.coefficientSmall moment
  have factored : fullKernelMoment parameters moment
      (actualRotatedSigmaBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall) ≤
      constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 6) := by
    simpa only [constant, Finset.sum_mul, mul_assoc] using estimated
  exact factored.trans (mul_le_mul (le_abs_self constant)
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment + 6 ≤ moment + 7))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant))

theorem actualSigmaComponentBoundaryKernel_vanishingMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (component : Fin 3) :
    BoundaryDeviationMoments parameters L compactRadius
      (fun state => actualSigmaComponentBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (boundaryScalarMultiplicationKernel_moment_le parameters 1 moment
    (actualSigmaBoundaryCoefficients parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component)
    (actualSigmaBoundaryCoefficients_moments parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component)).trans
  have estimated : Real.exp (parameters.sigma0 + parameters.gamma) *
      (∑' frequency, productMoment parameters moment 1
        (actualSigmaBoundaryCoefficients parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component) frequency) ≤
      constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 5) := by
    unfold constant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact sigmaScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall component moment 0 1 zero_le_one le_rfl
  exact estimated.trans (mul_le_mul (le_abs_self constant)
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment + 5 ≤ moment + 7))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant))

theorem actualRotatedSigmaComponentBoundaryKernel_vanishingMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (component : Fin 3) :
    BoundaryDeviationMoments parameters L compactRadius
      (fun state => actualRotatedSigmaComponentBoundaryKernel parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (boundaryScalarMultiplicationKernel_moment_le parameters 1 moment
    (actualRotatedSigmaBoundaryCoefficients parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component)
    (actualRotatedSigmaBoundaryCoefficients_moments parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component)).trans
  have estimated : Real.exp (parameters.sigma0 + parameters.gamma) *
      (∑' frequency, productMoment parameters moment 1
        (actualRotatedSigmaBoundaryCoefficients parameters L state.val.rho state.val.epsilon state.val.field state.val.coefficientSmall component) frequency) ≤
      constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 6) := by
    unfold constant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (sigmaAngularScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field
        state.val.coefficientSmall component moment 0 1 zero_le_one le_rfl).2
  exact estimated.trans (mul_le_mul (le_abs_self constant)
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment + 6 ≤ moment + 7))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant))

theorem boundaryDeviationMultiplier_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.deltaRow) := by
  intro moment
  refine ⟨boundaryDeviationMultiplierConstant parameters L compact moment,
    boundaryDeviationMultiplierConstant_nonnegative parameters L compact moment, ?_⟩
  intro state
  apply (boundaryDeviationMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall moment).trans
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))
    (boundaryDeviationMultiplierConstant_nonnegative parameters L compact moment)

theorem boundaryRotatedDeviationMultiplier_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.rotatedDeltaRow) := by
  intro moment
  refine ⟨boundaryDeviationMultiplierConstant parameters L compact (moment + 1),
    boundaryDeviationMultiplierConstant_nonnegative parameters L compact (moment + 1), ?_⟩
  intro state
  apply (boundaryRotatedDeviationMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall moment).trans
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))
    (boundaryDeviationMultiplierConstant_nonnegative parameters L compact (moment + 1))

end Grad.ActualBoundaryInverse
