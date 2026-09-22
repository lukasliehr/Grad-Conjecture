import BKC20PhysicalMomentFamilies

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives

theorem actualGaugeRowsKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualGaugeRowsKernel parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon state.field state.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 3,
      gaugeScalarConstant parameters L compactRadius row column moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (boundaryMatrixMultiplicationKernel_moment_le parameters 3 2 moment
    (actualGaugeRowsCoefficients parameters L state.rho state.alpha state.delta
      state.parameter state.epsilon state.field state.coefficientSmall)
    (actualGaugeRowsCoefficients_moments parameters L state.rho state.alpha state.delta
      state.parameter state.epsilon state.field state.coefficientSmall)).trans
  have estimated :
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin 2, ∑ column : Fin 3,
          ∑' shift, productMoment parameters moment 1
            (actualGaugeRowsCoefficients parameters L state.rho state.alpha state.delta
              state.parameter state.epsilon state.field state.coefficientSmall row column) shift ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 5) := by
    unfold constant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro row _
    apply Finset.sum_le_sum
    intro column _
    exact gaugeScalarMoment_bound parameters L state.rho state.alpha state.delta
      state.parameter state.epsilon state.field state.coefficientSmall compactRadius
      row column moment 0 1 zero_le_one le_rfl state.compactNonnegative
      state.alphaSmall state.deltaSmall state.parameterSmall
  exact estimated.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 5) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

theorem actualGammaDeviationKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualGammaDeviationKernel parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon state.field state.coefficientSmall) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 2,
      gaugeScalarConstant parameters L compactRadius row column.succ moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  have estimated := actualGammaDeviationKernel_moment_le parameters L state.rho
    state.alpha state.delta state.parameter state.epsilon compactRadius state.field
    state.coefficientSmall state.compactNonnegative state.alphaSmall state.deltaSmall
    state.parameterSmall moment
  have factored : fullKernelMoment parameters moment
      (actualGammaDeviationKernel parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon state.field state.coefficientSmall) ≤
      constant * physicalBudget parameters state.field state.rho state.epsilon (moment + 5) := by
    simpa only [constant, Finset.sum_mul, mul_assoc] using estimated
  exact factored.trans (mul_le_mul (le_abs_self constant)
    (state.budget_le_size moment (moment + 5) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant))

theorem actualNegativeGammaInverseKernelOnBall_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualNegativeGammaInverseKernelOnBall parameters L state.rho
        state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.gaugeSmall state.compactNonnegative state.alphaSmall state.deltaSmall
        state.parameterSmall) := by
  unfold actualNegativeGammaInverseKernelOnBall actualNegativeGammaInverseKernel
  apply UniformKernelMoments.negativeIdentityInverse BoundaryReconstructionState.one_le_size
  exact (actualGammaDeviationKernel_physicalMoments parameters L compactRadius).neg

theorem actualGaugeQKernelOnBall_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualGaugeQKernelOnBall parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon compactRadius state.field state.gaugeSmall
        state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualGaugeQKernelOnBall actualGaugeCorrectionKernelOnBall actualGaugeMeanRowsKernel
  apply UniformKernelMoments.add
  · exact PhysicalKernelMoments.fixed parameters L compactRadius _
  · apply PhysicalKernelMoments.comp
    · exact PhysicalKernelMoments.fixed parameters L compactRadius _
    · apply PhysicalKernelMoments.comp
      · exact actualNegativeGammaInverseKernelOnBall_physicalMoments parameters L compactRadius
      · apply PhysicalKernelMoments.comp
        · exact PhysicalKernelMoments.fixed parameters L compactRadius _
        · exact actualGaugeRowsKernel_physicalMoments parameters L compactRadius

end Grad.BoundaryKernelAction
