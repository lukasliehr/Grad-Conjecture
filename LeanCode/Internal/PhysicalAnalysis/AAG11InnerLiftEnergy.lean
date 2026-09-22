import AAG10InnerLiftProfile

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.CircularHighWeak Grad.BoundaryLift

def annularPotentialUpperConstant (lower length : ℝ) : ℝ := lower⁻¹ ^ 2 + length⁻¹ ^ 2

theorem annularPotential_upper (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    annularPotential length radius mode.val.1 mode.val.2 ≤
      annularPotentialUpperConstant lower length * annularFrequency mode.val.1 mode.val.2 ^ 2 := by
  have modeBound : |(mode.val.1 : ℝ)| ≤ annularFrequency mode.val.1 mode.val.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.val.2 : ℝ)]
  have cellBound : |(mode.val.2 : ℝ)| ≤ annularFrequency mode.val.1 mode.val.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ)]
  have modeSq : (mode.val.1 : ℝ) ^ 2 ≤ annularFrequency mode.val.1 mode.val.2 ^ 2 := by
    nlinarith [sq_abs (mode.val.1 : ℝ), abs_nonneg (mode.val.1 : ℝ)]
  have cellSq : (mode.val.2 : ℝ) ^ 2 ≤ annularFrequency mode.val.1 mode.val.2 ^ 2 := by
    nlinarith [sq_abs (mode.val.2 : ℝ), abs_nonneg (mode.val.2 : ℝ)]
  have radiusSq : lower ^ 2 ≤ radius ^ 2 := by nlinarith [inside.1]
  have modePart := (div_le_div_of_nonneg_left (sq_nonneg (mode.val.1 : ℝ))
    (sq_pos_of_pos positive) radiusSq).trans (div_le_div_of_nonneg_right modeSq (sq_nonneg lower))
  have multiplier := mul_le_of_le_one_left (sq_nonneg (mode.val.2 : ℝ)) (highMultiplier_one_le mode.val.1)
  have cellPart := div_le_div_of_nonneg_right (multiplier.trans cellSq) (sq_nonneg length)
  unfold annularPotential annularPotentialUpperConstant
  simpa only [div_eq_mul_inv, inv_pow] using (add_le_add modePart cellPart).trans_eq (by ring)

def annularInnerLiftSquaredConstant (lower length : ℝ) : ℝ :=
  ((annularInnerCutoffDerivativeBound lower + 1) ^ 2 + annularPotentialUpperConstant lower length) / 2

theorem annularInnerLiftSquaredConstant_nonnegative (lower length : ℝ) :
    0 ≤ annularInnerLiftSquaredConstant lower length := by
  unfold annularInnerLiftSquaredConstant annularPotentialUpperConstant
  positivity

theorem annularInnerLiftProfile_energy_pointwise (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    radius * (deriv (annularInnerLiftProfile lower mode) radius ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 * annularInnerLiftProfile lower mode radius ^ 2) ≤
      (2 * annularInnerLiftSquaredConstant lower length * annularFrequency mode.val.1 mode.val.2) *
        Real.exp (-(2 * annularFrequency mode.val.1 mode.val.2) * (radius - lower)) := by
  let frequency := annularFrequency mode.val.1 mode.val.2
  let decay := Real.exp (-frequency * (radius - lower))
  let cutBound := annularInnerCutoffDerivativeBound lower + 1
  let potentialBound := annularPotentialUpperConstant lower length
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le (annularFrequency_one_le _ _)
  have rootPositive := Real.sqrt_pos.mpr frequencyPositive
  have rootSq : Real.sqrt frequency ^ 2 = frequency := Real.sq_sqrt frequencyPositive.le
  have cutPositive : 0 < cutBound := by
    dsimp [cutBound]
    linarith [annularInnerCutoffDerivativeBound_nonnegative lower]
  have valueBound := annularInnerLiftProfile_abs_bound lower mode radius
  have derivativeBound := annularInnerLiftProfile_deriv_bound lower mode radius inside
  have valueSq : annularInnerLiftProfile lower mode radius ^ 2 ≤ decay ^ 2 / frequency := by
    have squared := (sq_le_sq₀ (abs_nonneg _) (div_nonneg (Real.exp_pos _).le rootPositive.le)).mpr valueBound
    simpa only [sq_abs, div_pow, rootSq] using squared
  have derivativeSq : deriv (annularInnerLiftProfile lower mode) radius ^ 2 ≤
      cutBound ^ 2 * frequency * decay ^ 2 := by
    have squared := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ cutBound * frequency * decay / Real.sqrt frequency)).mpr derivativeBound
    have normalization : (cutBound * frequency * decay / Real.sqrt frequency) ^ 2 =
        cutBound ^ 2 * frequency * decay ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, rootSq]
      field_simp
    have squared' : deriv (annularInnerLiftProfile lower mode) radius ^ 2 ≤
        (cutBound * frequency * decay / Real.sqrt frequency) ^ 2 := by simpa only [sq_abs] using squared
    exact squared'.trans_eq normalization
  have potential := annularPotential_upper lower length positive mode radius inside
  have potentialNonnegative := (annularPotential_pos length radius mode.val.1 mode.val.2 mode.property
    (positive.trans_le inside.1)).le
  have mass := mul_le_mul potential valueSq (sq_nonneg _) (by
    exact mul_nonneg (by unfold annularPotentialUpperConstant; positivity) (sq_nonneg frequency))
  have normalization : (potentialBound * frequency ^ 2) * (decay ^ 2 / frequency) =
      potentialBound * frequency * decay ^ 2 := by field_simp
  rw [normalization] at mass
  have radial := mul_le_of_le_one_left
    (add_nonneg (sq_nonneg (deriv (annularInnerLiftProfile lower mode) radius))
      (mul_nonneg potentialNonnegative (sq_nonneg (annularInnerLiftProfile lower mode radius)))) inside.2
  have decaySq : decay ^ 2 = Real.exp (-(2 * frequency) * (radius - lower)) := by
    dsimp [decay]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change _ ≤ (2 * annularInnerLiftSquaredConstant lower length * frequency) * _
  rw [← decaySq]
  unfold annularInnerLiftSquaredConstant
  dsimp [cutBound, potentialBound] at derivativeSq mass
  nlinarith only [radial, derivativeSq, mass]

theorem annularInnerLiftProfile_energy_integral (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) :
    (∫ radius in lower..1, radius * (deriv (annularInnerLiftProfile lower mode) radius ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 * annularInnerLiftProfile lower mode radius ^ 2)) ≤
      annularInnerLiftSquaredConstant lower length := by
  let frequency := annularFrequency mode.val.1 mode.val.2
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le (annularFrequency_one_le _ _)
  have smooth := annularInnerLiftProfile_smooth lower mode
  have derivativeContinuous := (contDiff_infty_iff_deriv.mp smooth).2.continuous
  have integrable : IntervalIntegrable
      (fun radius => radius * (deriv (annularInnerLiftProfile lower mode) radius ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 * annularInnerLiftProfile lower mode radius ^ 2)) volume lower 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le bounded.le]
    exact continuousOn_id.mul ((derivativeContinuous.pow 2).continuousOn.add
      ((annularPotential_continuousOn lower length positive mode.val.1 mode.val.2).mul
        (smooth.continuous.pow 2).continuousOn))
  have exponentialContinuous : Continuous (fun radius : ℝ =>
      (2 * annularInnerLiftSquaredConstant lower length * frequency) * Real.exp (-(2 * frequency) * (radius - lower))) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on bounded.le integrable
    (exponentialContinuous.intervalIntegrable lower 1)
    (fun radius inside => annularInnerLiftProfile_energy_pointwise lower length positive mode radius inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have translation : (∫ radius in lower..1, Real.exp (-(2 * frequency) * (radius - lower))) =
      ∫ time in (0 : ℝ)..(1 - lower), Real.exp (-(2 * frequency) * time) := by
    simpa only [sub_self] using intervalIntegral.integral_comp_sub_right
      (fun time => Real.exp (-(2 * frequency) * time)) (a := lower) (b := 1) lower
  rw [translation] at comparison
  have exponential := exponential_decay_integral_le (2 * frequency) (1 - lower)
    (by positivity) (by linarith)
  have multiplied := mul_le_mul_of_nonneg_left exponential
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (annularInnerLiftSquaredConstant_nonnegative lower length)) frequencyPositive.le)
  apply comparison.trans (multiplied.trans_eq ?_)
  field_simp

end Grad.AnnularVariational
