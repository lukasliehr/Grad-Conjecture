import BL5ProfileBound

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem exponential_decay_integral_le (rate endpoint : ℝ) (ratePositive : 0 < rate)
    (endpointNonnegative : 0 ≤ endpoint) :
    (∫ time in (0 : ℝ)..endpoint, Real.exp (-rate * time)) ≤ rate⁻¹ := by
  have derivative : ∀ time : ℝ,
      HasDerivAt (fun source : ℝ => -Real.exp (-rate * source) / rate)
        (Real.exp (-rate * time)) time := by
    intro time
    apply (((hasDerivAt_id time).const_mul (-rate)).exp.neg.div_const rate).congr_deriv
    field_simp [ratePositive.ne']
    rfl
  have continuousExponential : Continuous (fun time : ℝ => Real.exp (-rate * time)) := by fun_prop
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le endpointNonnegative
    ((continuousExponential.neg.div_const rate).continuousOn)
    (fun time _ => derivative time) (continuousExponential.intervalIntegrable 0 endpoint)
  rw [fundamental]
  change -Real.exp (-rate * endpoint) / rate - (-Real.exp (-rate * 0) / rate) ≤ rate⁻¹
  simp only [mul_zero, Real.exp_zero, neg_div, one_div]
  linarith [div_pos (Real.exp_pos (-rate * endpoint)) ratePositive]

theorem conjugatedProfile_derivative_squared_bound (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ^ 2 ≤
      (profileDerivativeConstant order parameters.gamma ^ 2 * boundaryFrequency mode ^ (2 * order)) *
        Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * time) := by
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (conjugatedProfile_iterated_decay parameters mode order time inside) 2).trans_eq
  simp only [mul_pow, ← pow_mul]
  rw [show Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * time) ^ 2 =
      Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * time) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [Nat.mul_comm order 2]

theorem conjugatedProfile_derivative_integral_bound (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 4 : ℝ), ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ^ 2) ≤
      (profileDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        boundaryFrequency mode ^ (2 * order) / boundaryFrequency mode := by
  have squaredContinuous : Continuous (fun time =>
      ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ^ 2) := by
    have normContinuous : Continuous (fun time =>
        ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖) := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        ((conjugatedProfile_smooth parameters mode).continuous_iteratedFDeriv
          (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm
    exact (continuous_pow 2).comp normContinuous
  have exponentialContinuous : Continuous (fun time : ℝ =>
      (profileDerivativeConstant order parameters.gamma ^ 2 * boundaryFrequency mode ^ (2 * order)) *
        Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (squaredContinuous.intervalIntegrable _ _)
    (exponentialContinuous.intervalIntegrable _ _)
    (fun time inside => conjugatedProfile_derivative_squared_bound parameters mode order time inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have ratePositive : 0 < 2 * boundaryDecayRate parameters * boundaryFrequency mode :=
    mul_pos (mul_pos (by norm_num) (boundaryDecayRate_pos parameters)) (boundaryFrequency_pos mode)
  have integrated := mul_le_mul_of_nonneg_left
    (exponential_decay_integral_le _ (1 / 4) ratePositive (by norm_num))
    (mul_nonneg (sq_nonneg (profileDerivativeConstant order parameters.gamma))
      (pow_nonneg (boundaryFrequency_pos mode).le (2 * order)))
  apply (comparison.trans integrated).trans_eq
  ring

theorem conjugatedProfile_weighted_energy (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (grade order : ℕ) (gradePositive : 1 ≤ grade) (orderBound : order ≤ grade) :
    boundaryFrequency mode ^ (2 * (grade - order)) *
      (∫ time in (0 : ℝ)..(1 / 4 : ℝ), ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ^ 2) ≤
      (profileDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        boundaryFrequency mode ^ (2 * grade - 1) := by
  have preliminary := mul_le_mul_of_nonneg_left
    (conjugatedProfile_derivative_integral_bound parameters mode order)
    (pow_nonneg (boundaryFrequency_pos mode).le (2 * (grade - order)))
  apply preliminary.trans_eq
  have exponent : 2 * (grade - order) + 2 * order = 2 * grade := by omega
  have factor : boundaryFrequency mode ^ (2 * grade - 1) * boundaryFrequency mode =
      boundaryFrequency mode ^ (2 * grade) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ = (profileDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        ((boundaryFrequency mode ^ (2 * (grade - order)) * boundaryFrequency mode ^ (2 * order)) /
          boundaryFrequency mode) := by ring
    _ = _ := by rw [← pow_add, exponent, ← factor, mul_div_cancel_right₀ _ (boundaryFrequency_pos mode).ne']

end Grad.BoundaryLift
