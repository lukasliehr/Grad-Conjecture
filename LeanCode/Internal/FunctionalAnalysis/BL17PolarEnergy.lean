import BL16AngularTensor

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem angularFrequency_le_boundaryFrequency (mode : ℤ × ℤ) :
    |(mode.1 : ℝ)| ≤ boundaryFrequency mode := by
  apply (sq_le_sq₀ (abs_nonneg _) (boundaryFrequency_pos mode).le).mp
  rw [sq_abs, boundaryFrequency_sq]
  nlinarith [sq_nonneg (mode.2 : ℝ)]

def polarDerivativeConstant (order : ℕ) (gamma : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * profileDerivativeConstant index gamma

theorem polarDerivativeConstant_nonnegative (order : ℕ) (gamma : ℝ) (nonnegative : 0 ≤ gamma) :
    0 ≤ polarDerivativeConstant order gamma := by
  apply Finset.sum_nonneg
  intro index _
  exact mul_nonneg (Nat.cast_nonneg _) (profileDerivativeConstant_nonnegative index gamma nonnegative)

theorem polarModeField_iterated_decay {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) point‖ ≤
      polarDerivativeConstant order parameters.gamma * boundaryFrequency mode ^ order *
        Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * point.1) * ‖value‖ := by
  apply (polarModeField_iterated_bound parameters mode value order point).trans
  rw [polarDerivativeConstant, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index indexIn
  have indexBound : index ≤ order := by have := Finset.mem_range.mp indexIn; omega
  have radial := conjugatedProfile_iterated_decay parameters mode index point.1 inside
  have frequencyBound : boundaryFrequency mode ^ index * |(mode.1 : ℝ)| ^ (order - index) ≤
      boundaryFrequency mode ^ order := by
    calc
      _ ≤ boundaryFrequency mode ^ index * boundaryFrequency mode ^ (order - index) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (angularFrequency_le_boundaryFrequency mode) _)
          (pow_nonneg (boundaryFrequency_pos mode).le _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le indexBound]
  calc
    _ ≤ (order.choose index : ℝ) *
        (profileDerivativeConstant index parameters.gamma * boundaryFrequency mode ^ index *
          Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * point.1)) *
        |(mode.1 : ℝ)| ^ (order - index) * ‖value‖ := by gcongr
    _ = ((order.choose index : ℝ) * profileDerivativeConstant index parameters.gamma *
        Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * point.1) * ‖value‖) *
        (boundaryFrequency mode ^ index * |(mode.1 : ℝ)| ^ (order - index)) := by ring
    _ ≤ ((order.choose index : ℝ) * profileDerivativeConstant index parameters.gamma *
        Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * point.1) * ‖value‖) *
        boundaryFrequency mode ^ order := by
      apply mul_le_mul_of_nonneg_left frequencyBound
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (profileDerivativeConstant_nonnegative index parameters.gamma parameters.gamma_pos.le))
        (Real.exp_pos _).le) (norm_nonneg _)
    _ = _ := by ring

theorem polarModeField_squared_decay {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) point‖ ^ 2 ≤
      (polarDerivativeConstant order parameters.gamma ^ 2 * boundaryFrequency mode ^ (2 * order) * ‖value‖ ^ 2) *
        Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * point.1) := by
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (polarModeField_iterated_decay parameters mode value order point inside) 2).trans_eq
  simp only [mul_pow, ← pow_mul]
  rw [show Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * point.1) ^ 2 =
      Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * point.1) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  ring

theorem polarModeField_radial_integral {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 4 : ℝ),
      ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0)‖ ^ 2) ≤
      (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        boundaryFrequency mode ^ (2 * order) / boundaryFrequency mode * ‖value‖ ^ 2 := by
  have normContinuous : Continuous (fun time : ℝ =>
      ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0)‖ ^ 2) :=
    ((((polarModeField_smooth parameters mode value).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
        (continuous_id.prodMk continuous_const)).norm).pow 2
  have exponentialContinuous : Continuous (fun time : ℝ =>
      (polarDerivativeConstant order parameters.gamma ^ 2 * boundaryFrequency mode ^ (2 * order) * ‖value‖ ^ 2) *
        Real.exp (-(2 * boundaryDecayRate parameters * boundaryFrequency mode) * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (normContinuous.intervalIntegrable _ _) (exponentialContinuous.intervalIntegrable _ _)
    (fun time inside => polarModeField_squared_decay parameters mode value order (time, 0) inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have ratePositive : 0 < 2 * boundaryDecayRate parameters * boundaryFrequency mode :=
    mul_pos (mul_pos (by norm_num) (boundaryDecayRate_pos parameters)) (boundaryFrequency_pos mode)
  have integrated := mul_le_mul_of_nonneg_left
    (exponential_decay_integral_le _ (1 / 4) ratePositive (by norm_num))
    (mul_nonneg (mul_nonneg (sq_nonneg (polarDerivativeConstant order parameters.gamma))
      (pow_nonneg (boundaryFrequency_pos mode).le (2 * order))) (sq_nonneg ‖value‖))
  apply (comparison.trans integrated).trans_eq
  ring

theorem polarModeField_weighted_energy {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (grade order : ℕ) (gradePositive : 1 ≤ grade)
    (orderBound : order ≤ grade) :
    cellFrequency mode.2 ^ (2 * (grade - order)) *
      (∫ time in (0 : ℝ)..(1 / 4 : ℝ),
        ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0)‖ ^ 2) ≤
      (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        boundaryFrequency mode ^ (2 * grade - 1) * ‖value‖ ^ 2 := by
  have preliminary := mul_le_mul_of_nonneg_left (polarModeField_radial_integral parameters mode value order)
    (pow_nonneg (cellFrequency_pos mode.2).le (2 * (grade - order)))
  have frequencyBound := pow_le_pow_left₀ (cellFrequency_pos mode.2).le
    (cellFrequency_le_boundaryFrequency mode) (2 * (grade - order))
  have nonnegative : 0 ≤ (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
      boundaryFrequency mode ^ (2 * order) / boundaryFrequency mode * ‖value‖ ^ 2 := by
    have decayPositive := boundaryDecayRate_pos parameters
    have frequencyPositive := boundaryFrequency_pos mode
    positivity
  apply (preliminary.trans (mul_le_mul_of_nonneg_right frequencyBound nonnegative)).trans_eq
  have exponent : 2 * (grade - order) + 2 * order = 2 * grade := by omega
  have factor : boundaryFrequency mode ^ (2 * grade - 1) * boundaryFrequency mode =
      boundaryFrequency mode ^ (2 * grade) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ = (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
        ((boundaryFrequency mode ^ (2 * (grade - order)) * boundaryFrequency mode ^ (2 * order)) /
          boundaryFrequency mode) * ‖value‖ ^ 2 := by ring
    _ = _ := by rw [← pow_add, exponent, ← factor, mul_div_cancel_right₀ _ (boundaryFrequency_pos mode).ne']

end Grad.BoundaryLift
