import AHP27RadialGaugePhysicalMoments

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation Grad.PhaseAlgebra

theorem radialScalarKernel_moment_le (parameters : PhaseParameters) (r : RadialPoint)
    (dimension moment : ℕ) (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ order, Summable (productMoment parameters order r.val coefficient)) :
    fullKernelMoment (radialKernelParameters parameters r) moment
      (radialScalarKernel parameters r dimension coefficient moments) ≤
      Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑' shift, productMoment parameters moment r.val coefficient shift := by
  have bound := boundaryScalarMultiplicationKernel_moment_le
    (radialKernelParameters parameters r) dimension moment coefficient
    (fun order => by simpa only [radialKernelProductMoment] using moments order)
  simp only [radialKernelProductMoment] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right (radialKernelPhaseConstant_le parameters r)
    (tsum_nonneg (productMoment_nonnegative parameters moment r.val _)))

theorem radialRotatedSigmaKernel_moment_le (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint) (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
      (radialRotatedSigmaKernel parameters L compact state r 0) ≤
      (Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑ component : Fin 3, sigmaScalarConstant parameters L component (moment + 1) 0) *
      physicalBudget parameters state.field state.rho state.epsilon (moment + 6) := by
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have each (component : Fin 3) := (sigmaAngularScalarMoment_bound parameters L state.rho
    state.epsilon state.field state.low component moment 0 r.val r.property.1 r.property.2).2
  have summed := Finset.sum_le_sum (s := Finset.univ) fun component _ => each component
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  simp only [← Finset.sum_mul]
  ring

theorem radialSigmaKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialSigmaKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  exact (radialSigmaKernel_moment_le parameters L compact state.val r 0 moment).trans
    (mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 0 + 5) (by omega))
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
      (abs_nonneg constant))

theorem radialRotatedSigmaKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialRotatedSigmaKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  exact (radialRotatedSigmaKernel_moment_le parameters L compact state.val r moment).trans
    (mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 6) (by omega))
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
      (abs_nonneg constant))

theorem radialSigmaComponentKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) : RadialPhysicalMoments parameters L compact
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
  exact mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 0 + 5) (by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialRotatedSigmaComponentKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) (component : Fin 3) :
    RadialPhysicalMoments parameters L compact
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
  exact mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 0 + 6) (by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

end Grad.AnnularReconstruction
