import BT13CoefficientCalculus

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

theorem two_term_pow_bound (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (order : ℕ) :
    (first + second) ^ order ≤ (2 : ℝ) ^ order * (first ^ order + second ^ order) := by
  rcases le_total first second with ordered | ordered
  · calc
      _ ≤ (2 * second) ^ order := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ order * second ^ order := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg firstNonnegative _)) (by positivity)
  · calc
      _ ≤ (2 * first) ^ order := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ order * first ^ order := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg secondNonnegative _)) (by positivity)

theorem boundaryFrequency_even_bound (mode : ℤ × ℤ) (order : ℕ) :
    boundaryFrequency mode ^ (2 * order) ≤ (2 : ℝ) ^ order *
      (cellFrequency mode.2 ^ (2 * order) + |(mode.1 : ℝ)| ^ (2 * order)) := by
  have identity : boundaryFrequency mode ^ 2 = cellFrequency mode.2 ^ 2 + |(mode.1 : ℝ)| ^ 2 := by
    rw [boundaryFrequency_sq, cellFrequency_formula, Real.sq_sqrt (by positivity), sq_abs]
    ring
  rw [pow_mul, identity]
  simpa only [← pow_mul] using two_term_pow_bound (cellFrequency mode.2 ^ 2) (|(mode.1 : ℝ)| ^ 2)
    (sq_nonneg _) (sq_nonneg _) order

theorem half_weight_energy_bound {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (curve derivative : ℝ → Value) (frequency : ℝ) (positive : 0 < frequency)
    (grade : ℕ) (gradePositive : 1 ≤ grade)
    (curveContinuous : Continuous curve) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo (0 : ℝ) (1 / 4), HasDerivAt curve (derivative time) time)
    (vanishes : curve (1 / 4) = 0) :
    frequency ^ (2 * grade - 1) * ‖curve 0‖ ^ 2 ≤
      frequency ^ (2 * grade) * (∫ time in (0 : ℝ)..(1 / 4 : ℝ), ‖curve time‖ ^ 2) +
      frequency ^ (2 * (grade - 1)) * (∫ time in (0 : ℝ)..(1 / 4 : ℝ), ‖derivative time‖ ^ 2) := by
  have energy := mul_le_mul_of_nonneg_left (collar_energy_bound curve derivative (1 / 4) frequency
    (by norm_num) positive curveContinuous derivativeContinuous differentiates vanishes)
    (pow_nonneg positive.le (2 * grade - 1))
  have first : frequency ^ (2 * grade - 1) * frequency = frequency ^ (2 * grade) := by
    rw [← pow_succ]
    congr 1
    omega
  have second : frequency ^ (2 * grade - 1) * frequency⁻¹ = frequency ^ (2 * (grade - 1)) := by
    rw [show 2 * grade - 1 = 2 * (grade - 1) + 1 by omega, pow_succ,
      mul_assoc, mul_inv_cancel₀ positive.ne', mul_one]
  simpa only [mul_add, ← mul_assoc, first, second] using energy

theorem collarIntegral_swap (function : ℝ × ℝ → ℝ) (continuousFunction : Continuous function) :
    (∫ time in (0 : ℝ)..(1 / 4 : ℝ), ∫ angle in -Real.pi..Real.pi, function (time, angle)) =
      collarIntegral function := by
  have integrable : Integrable function
      ((volume.restrict (Icc (0 : ℝ) (1 / 4))).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact continuousFunction.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have swap := integral_integral_swap (f := fun time angle : ℝ => function (time, angle)) integrable
  unfold collarIntegral
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4),
    intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp_rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact swap

end Grad.BoundaryTrace
