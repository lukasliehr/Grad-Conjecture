import BKC23ReconstructionPhysicalMoments

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives

theorem actualSigmaBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualSigmaBoundaryKernel parameters L state.rho state.epsilon state.field
        state.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  have estimated := actualSigmaBoundaryKernel_moment_le parameters L state.rho state.epsilon
    state.field state.coefficientSmall moment
  have factored : fullKernelMoment parameters moment
      (actualSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall) ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 5) := by
    simpa only [constant, Finset.sum_mul, mul_assoc] using estimated
  exact factored.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 5) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

theorem actualRotatedSigmaBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualRotatedSigmaBoundaryKernel parameters L state.rho state.epsilon state.field
        state.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  have estimated := actualRotatedSigmaBoundaryKernel_moment_le parameters L state.rho state.epsilon
    state.field state.coefficientSmall moment
  have factored : fullKernelMoment parameters moment
      (actualRotatedSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall) ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 6) := by
    simpa only [constant, Finset.sum_mul, mul_assoc] using estimated
  exact factored.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 6) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

theorem actualSigmaComponentBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (component : Fin 3) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field
        state.coefficientSmall component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (boundaryScalarMultiplicationKernel_moment_le parameters 1 moment
    (actualSigmaBoundaryCoefficients parameters L state.rho state.epsilon state.field state.coefficientSmall component)
    (actualSigmaBoundaryCoefficients_moments parameters L state.rho state.epsilon state.field state.coefficientSmall component)).trans
  have estimated : Real.exp (parameters.sigma0 + parameters.gamma) *
      (∑' frequency, productMoment parameters moment 1
        (actualSigmaBoundaryCoefficients parameters L state.rho state.epsilon state.field state.coefficientSmall component) frequency) ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 5) := by
    unfold constant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact sigmaScalarMoment_bound parameters L state.rho state.epsilon state.field
        state.coefficientSmall component moment 0 1 zero_le_one le_rfl
  exact estimated.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 5) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

theorem actualRotatedSigmaComponentBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (component : Fin 3) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualRotatedSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field
        state.coefficientSmall component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (boundaryScalarMultiplicationKernel_moment_le parameters 1 moment
    (actualRotatedSigmaBoundaryCoefficients parameters L state.rho state.epsilon state.field state.coefficientSmall component)
    (actualRotatedSigmaBoundaryCoefficients_moments parameters L state.rho state.epsilon state.field state.coefficientSmall component)).trans
  have estimated : Real.exp (parameters.sigma0 + parameters.gamma) *
      (∑' frequency, productMoment parameters moment 1
        (actualRotatedSigmaBoundaryCoefficients parameters L state.rho state.epsilon state.field state.coefficientSmall component) frequency) ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 6) := by
    unfold constant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (sigmaAngularScalarMoment_bound parameters L state.rho state.epsilon state.field
        state.coefficientSmall component moment 0 1 zero_le_one le_rfl).2
  exact estimated.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 6) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

end Grad.BoundaryKernelAction
