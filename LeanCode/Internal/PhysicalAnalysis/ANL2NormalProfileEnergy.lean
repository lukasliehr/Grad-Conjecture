import ANL1NormalProfile

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift

/-- Absorb the linear time factor while retaining half the exponential decay. -/
theorem time_exponential_bound (rate time : ℝ) (positive : 0 < rate) :
    (rate⁻¹ + time) * Real.exp (-rate * time) ≤
      (2 / rate) * Real.exp (-rate * time / 2) := by
  have exponential := Real.add_one_le_exp (rate * time / 2)
  have linear : rate⁻¹ + time ≤ (2 / rate) * Real.exp (rate * time / 2) := by
    apply (mul_le_mul_iff_left₀ positive).mp
    field_simp
    nlinarith
  have comparison := mul_le_mul_of_nonneg_right linear (Real.exp_pos (-rate * time)).le
  apply comparison.trans_eq
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem normalProfile_decay_bound (mode : ℤ) (order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv order (normalProfile mode) time‖ ≤
      (2 * normalProfileConstant order) * boundaryFrequency (mode, 0) ^ order /
        boundaryFrequency (mode, 0) * Real.exp (-boundaryFrequency (mode, 0) * time / 2) := by
  have comparison := mul_le_mul_of_nonneg_left
    (time_exponential_bound (boundaryFrequency (mode, 0)) time (boundaryFrequency_pos (mode, 0)))
    (mul_nonneg (normalProfileConstant_nonnegative order) (pow_nonneg (boundaryFrequency_pos (mode, 0)).le order))
  have previous := normalProfile_bound mode order time inside
  apply previous.trans
  apply (show normalProfileConstant order * boundaryFrequency (mode, 0) ^ order *
      ((boundaryFrequency (mode, 0))⁻¹ + time) * Real.exp (-boundaryFrequency (mode, 0) * time) ≤
      normalProfileConstant order * boundaryFrequency (mode, 0) ^ order *
        ((2 / boundaryFrequency (mode, 0)) * Real.exp (-boundaryFrequency (mode, 0) * time / 2)) by
    simpa only [mul_assoc] using comparison).trans_eq
  ring

def normalEnergyConstant (order : ℕ) : ℝ := 4 * normalProfileConstant order ^ 2

theorem normalEnergyConstant_nonnegative (order : ℕ) : 0 ≤ normalEnergyConstant order :=
  mul_nonneg (by norm_num) (sq_nonneg _)

theorem normalProfile_squared_bound (mode : ℤ) (order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv order (normalProfile mode) time‖ ^ 2 ≤
      (normalEnergyConstant order * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 2) * Real.exp (-boundaryFrequency (mode, 0) * time) := by
  have squared := pow_le_pow_left₀ (norm_nonneg _) (normalProfile_decay_bound mode order time inside) 2
  apply squared.trans_eq
  rw [mul_pow, div_pow, mul_pow, mul_pow, ← pow_mul, mul_comm order 2]
  have exponential : Real.exp (-boundaryFrequency (mode, 0) * time / 2) ^ 2 =
      Real.exp (-boundaryFrequency (mode, 0) * time) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [exponential]
  unfold normalEnergyConstant
  ring

theorem normalProfile_integral_bound (mode : ℤ) (order : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖iteratedDeriv order (normalProfile mode) time‖ ^ 2) ≤
      normalEnergyConstant order * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 3 := by
  have derivativeContinuous : Continuous (fun time => ‖iteratedDeriv order (normalProfile mode) time‖ ^ 2) := by
    have normContinuous : Continuous (fun time => ‖iteratedDeriv order (normalProfile mode) time‖) := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        ((normalProfile_smooth mode).continuous_iteratedFDeriv
          (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm
    exact normContinuous.pow 2
  have decayContinuous : Continuous (fun time : ℝ =>
      (normalEnergyConstant order * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 2) * Real.exp (-boundaryFrequency (mode, 0) * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (derivativeContinuous.intervalIntegrable _ _) (decayContinuous.intervalIntegrable _ _)
    (fun time inside => normalProfile_squared_bound mode order time inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have integrated := mul_le_mul_of_nonneg_left
    (exponential_decay_integral_le (boundaryFrequency (mode, 0)) (1 / 2) (boundaryFrequency_pos (mode, 0)) (by norm_num))
    (div_nonneg (mul_nonneg (normalEnergyConstant_nonnegative order)
      (pow_nonneg (boundaryFrequency_pos (mode, 0)).le (2 * order))) (sq_nonneg (boundaryFrequency (mode, 0))))
  apply (comparison.trans integrated).trans_eq
  ring

theorem normalProfile_weighted_energy (mode : ℤ) (grade order : ℕ)
    (gradeBound : 2 ≤ grade) (orderBound : order ≤ grade) :
    boundaryFrequency (mode, 0) ^ (2 * (grade - order)) *
      (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖iteratedDeriv order (normalProfile mode) time‖ ^ 2) ≤
      normalEnergyConstant order * boundaryFrequency (mode, 0) ^ (2 * grade - 3) := by
  have preliminary := mul_le_mul_of_nonneg_left (normalProfile_integral_bound mode order)
    (pow_nonneg (boundaryFrequency_pos (mode, 0)).le (2 * (grade - order)))
  apply preliminary.trans_eq
  have exponent : 2 * (grade - order) + 2 * order = 2 * grade := by omega
  have factor : boundaryFrequency (mode, 0) ^ (2 * grade - 3) * boundaryFrequency (mode, 0) ^ 3 =
      boundaryFrequency (mode, 0) ^ (2 * grade) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = normalEnergyConstant order *
        ((boundaryFrequency (mode, 0) ^ (2 * (grade - order)) * boundaryFrequency (mode, 0) ^ (2 * order)) /
          boundaryFrequency (mode, 0) ^ 3) := by ring
    _ = _ := by rw [← pow_add, exponent, ← factor,
      mul_div_cancel_right₀ _ (pow_ne_zero _ (boundaryFrequency_pos (mode, 0)).ne')]

end Grad.CircularNormalLift
