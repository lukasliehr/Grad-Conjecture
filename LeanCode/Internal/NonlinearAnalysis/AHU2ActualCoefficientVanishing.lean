import AHU1RadialVanishingMomentAllocation

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

theorem radialForceKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) : RadialDeviationMoments parameters L compact
      (fun state r => radialForceKernel parameters L compact state.val r kind 0) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    forceFourierConstant parameters L kind moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialForceKernel_moment_le parameters L compact state.val r kind 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 0 + 6 ≤ moment + 7 by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialRotatedForceKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) : RadialDeviationMoments parameters L compact
      (fun state r => radialRotatedForceKernel parameters L compact state.val r kind 0) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    forceFourierConstant parameters L kind (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialRotatedForceKernel_moment_le parameters L compact state.val r kind 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 1 + 0 + 6 ≤ moment + 7 by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialGaugeRowsKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialGaugeRowsKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 3, gaugeScalarConstant parameters L compact row column moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialGaugeRowsKernel_moment_le parameters L compact state.val r 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 0 + 5 ≤ moment + 7 by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialGammaDeviationKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialGammaDeviationKernel parameters L compact state.val r) := by
  intro moment
  refine ⟨radialGammaMomentConstant parameters L compact moment,
    radialGammaMomentConstant_nonnegative _ _ _ _, ?_⟩
  intro state r
  exact (radialGammaDeviationKernel_moment_le parameters L compact state.val r moment).trans
    (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 5 ≤ moment + 7 by omega))
      (radialGammaMomentConstant_nonnegative _ _ _ _))

theorem radialSigmaKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialSigmaKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  exact (radialSigmaKernel_moment_le parameters L compact state.val r 0 moment).trans
    (mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 0 + 5 ≤ moment + 7 by omega))
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
      (abs_nonneg constant))

theorem radialRotatedSigmaKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialRotatedSigmaKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  exact (radialRotatedSigmaKernel_moment_le parameters L compact state.val r moment).trans
    (mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 6 ≤ moment + 7 by omega))
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
      (abs_nonneg constant))

theorem radialSigmaComponentKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) : RadialDeviationMoments parameters L compact
      (fun state r => radialSigmaComponentKernel parameters L compact state.val r component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialScalarKernel_moment_le parameters r 1 moment _ _).trans
  have bound := mul_le_mul_of_nonneg_left
    (radialSigmaCoefficients_bound parameters L compact state.val r component 0 moment)
    (Real.exp_pos (parameters.sigma0 + 2 * parameters.gamma)).le
  apply bound.trans
  rw [← mul_assoc]
  exact mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 0 + 5 ≤ moment + 7 by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialRotatedSigmaComponentKernel_vanishingMoments
    (parameters : PhaseParameters) (L compact : ℝ) (component : Fin 3) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialRotatedSigmaComponentKernel parameters L compact state.val r component) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialScalarKernel_moment_le parameters r 1 moment _ _).trans
  have bound := mul_le_mul_of_nonneg_left
    (sigmaAngularScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field
      state.val.low component moment 0 r.val r.property.1 r.property.2).2
    (Real.exp_pos (parameters.sigma0 + 2 * parameters.gamma)).le
  apply bound.trans
  rw [← mul_assoc]
  exact mul_le_mul (le_abs_self constant) (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (show moment + 0 + 6 ≤ moment + 7 by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

end Grad.AnnularReconstruction
