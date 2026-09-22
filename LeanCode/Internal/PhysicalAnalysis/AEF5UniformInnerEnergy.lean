import AEF4ScaledInnerProfile

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.BoundaryLift

def uniformInnerLiftSquaredConstant (length : ℝ) : ℝ := 4 + length⁻¹ ^ 2

theorem uniformInnerLiftSquaredConstant_nonnegative (length : ℝ) :
    0 ≤ uniformInnerLiftSquaredConstant length := by
  unfold uniformInnerLiftSquaredConstant
  positivity

private theorem uniformInnerLiftProfile_value_sq (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    uniformInnerLiftProfile lower mode radius ^ 2 ≤
      Real.exp (-(2 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
        (radius - lower)) /
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le
    (Grad.AnnularVariational.annularFrequency_one_le _ _)
  have estimate := uniformInnerLiftProfile_abs_bound lower positive lowerHalf mode radius inside
  have rightNonnegative : 0 ≤
      Real.exp (-(frequency / lower) * (radius - lower)) / Real.sqrt frequency :=
    div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have squared := (sq_le_sq₀ (abs_nonneg _) rightNonnegative).mpr estimate
  rw [sq_abs] at squared
  calc
    uniformInnerLiftProfile lower mode radius ^ 2 ≤
        (Real.exp (-(frequency / lower) * (radius - lower)) / Real.sqrt frequency) ^ 2 := squared
    _ = Real.exp (-(2 * frequency / lower) * (radius - lower)) / frequency := by
      rw [div_pow, Real.sq_sqrt frequencyPositive.le, pow_two, ← Real.exp_add]
      congr 1
      ring

private theorem uniformInnerLiftProfile_deriv_sq (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    deriv (uniformInnerLiftProfile lower mode) radius ^ 2 ≤
      (4 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower ^ 2) *
        Real.exp (-(2 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
          (radius - lower)) := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le
    (Grad.AnnularVariational.annularFrequency_one_le _ _)
  have estimate := uniformInnerLiftProfile_deriv_bound lower positive lowerHalf mode radius inside
  have rightNonnegative : 0 ≤
      (2 * frequency / lower) * Real.exp (-(frequency / lower) * (radius - lower)) /
        Real.sqrt frequency := by positivity
  have squared := (sq_le_sq₀ (abs_nonneg _) rightNonnegative).mpr estimate
  rw [sq_abs] at squared
  dsimp only [frequency] at squared ⊢
  apply squared.trans_eq
  rw [div_pow, mul_pow, div_pow, Real.sq_sqrt frequencyPositive.le,
    pow_two (Real.exp _), ← Real.exp_add]
  field_simp [positive.ne', frequencyPositive.ne']
  dsimp only [frequency]
  ring

private theorem uniformInnerLiftProfile_energy_pointwise (lower length : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    radius * (deriv (uniformInnerLiftProfile lower mode) radius ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 *
        uniformInnerLiftProfile lower mode radius ^ 2) ≤
    ((4 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower ^ 2) +
      (lower⁻¹ ^ 2 + length⁻¹ ^ 2) *
        Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) *
      (radius * Real.exp
        (-(2 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
          (radius - lower))) := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  let exponential := Real.exp (-(2 * frequency / lower) * (radius - lower))
  have radiusPositive := positive.trans_le inside.1
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le
    (Grad.AnnularVariational.annularFrequency_one_le _ _)
  have derivativeSq := uniformInnerLiftProfile_deriv_sq lower positive lowerHalf mode radius inside
  have valueSq := uniformInnerLiftProfile_value_sq lower positive lowerHalf mode radius inside
  have potentialPositive := annularPotential_pos length radius mode.val.1 mode.val.2 mode.property radiusPositive
  have potentialUpper := annularPotential_upper lower length positive mode radius inside
  have potentialConstantNonnegative : 0 ≤ lower⁻¹ ^ 2 + length⁻¹ ^ 2 := by positivity
  have massBound : annularPotential length radius mode.val.1 mode.val.2 *
      uniformInnerLiftProfile lower mode radius ^ 2 ≤
      ((lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency) * exponential := by
    calc
      _ ≤ ((lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency ^ 2) *
          (exponential / frequency) :=
        mul_le_mul potentialUpper valueSq (sq_nonneg _)
          (mul_nonneg potentialConstantNonnegative (sq_nonneg frequency))
      _ = ((lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency) * exponential := by
        field_simp [frequencyPositive.ne']
  have insideBound :
      deriv (uniformInnerLiftProfile lower mode) radius ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 *
          uniformInnerLiftProfile lower mode radius ^ 2 ≤
      (4 * frequency / lower ^ 2 + (lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency) * exponential := by
    exact (add_le_add derivativeSq massBound).trans_eq (by ring)
  calc
    _ ≤ radius * ((4 * frequency / lower ^ 2 +
        (lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency) * exponential) :=
      mul_le_mul_of_nonneg_left insideBound radiusPositive.le
    _ = _ := by dsimp only [frequency, exponential]; ring

theorem uniformInnerLiftProfile_energy_integral (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (mode : HighAnnularMode) :
    (∫ radius in lower..1, radius *
      (deriv (uniformInnerLiftProfile lower mode) radius ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 *
          uniformInnerLiftProfile lower mode radius ^ 2)) ≤
      uniformInnerLiftSquaredConstant length := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  let rate := 2 * frequency / lower
  let coefficient := 4 * frequency / lower ^ 2 +
    (lower⁻¹ ^ 2 + length⁻¹ ^ 2) * frequency
  have lowerOne : lower ≤ 1 := lowerHalf.trans (by norm_num)
  have frequencyOne : 1 ≤ frequency := Grad.AnnularVariational.annularFrequency_one_le _ _
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratePositive : 0 < rate := by dsimp only [rate]; positivity
  have coefficientNonnegative : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have integrandIntegrable : IntervalIntegrable (fun radius : ℝ => radius *
      (deriv (uniformInnerLiftProfile lower mode) radius ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 *
          uniformInnerLiftProfile lower mode radius ^ 2)) volume lower 1 := by
    have slopeContinuous := (contDiff_infty_iff_deriv.mp
      (uniformInnerLiftProfile_smooth lower mode)).2.continuous
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le lowerOne]
    exact continuousOn_id.mul ((slopeContinuous.pow 2).continuousOn.add
      ((annularPotential_continuousOn lower length positive mode.val.1 mode.val.2).mul
        ((uniformInnerLiftProfile_smooth lower mode).continuous.pow 2).continuousOn))
  have majorantContinuous : Continuous (fun radius : ℝ =>
      coefficient * (radius * Real.exp (-rate * (radius - lower)))) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on lowerOne
    integrandIntegrable
    (majorantContinuous.intervalIntegrable lower 1)
    (fun radius inside => uniformInnerLiftProfile_energy_pointwise lower length positive lowerHalf
      lengthPositive mode radius inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have radial := shifted_radial_exponential_le lower rate positive lowerOne ratePositive
  have radialScaled := mul_le_mul_of_nonneg_left radial coefficientNonnegative
  have radialFormula : lower * rate⁻¹ + rate⁻¹ ^ 2 =
      lower ^ 2 / (2 * frequency) + lower ^ 2 / (4 * frequency ^ 2) := by
    dsimp only [rate]
    field_simp [positive.ne', frequencyPositive.ne']
    ring
  rw [radialFormula] at radialScaled
  have frequencySq : frequency ≤ frequency ^ 2 := by nlinarith
  have secondBound : lower ^ 2 / (4 * frequency ^ 2) ≤ lower ^ 2 / (4 * frequency) := by
    apply div_le_div_of_nonneg_left (sq_nonneg lower)
    · positivity
    · exact mul_le_mul_of_nonneg_left frequencySq (by norm_num)
  have radialSimple : lower ^ 2 / (2 * frequency) + lower ^ 2 / (4 * frequency ^ 2) ≤
      3 * lower ^ 2 / (4 * frequency) := by
    calc
      _ ≤ lower ^ 2 / (2 * frequency) + lower ^ 2 / (4 * frequency) := add_le_add_right secondBound _
      _ = 3 * lower ^ 2 / (4 * frequency) := by ring
  have multiplied := radialScaled.trans
    (mul_le_mul_of_nonneg_left radialSimple coefficientNonnegative)
  have productFormula : coefficient * (3 * lower ^ 2 / (4 * frequency)) =
      3 + (3 / 4) * (1 + lower ^ 2 / length ^ 2) := by
    dsimp only [coefficient]
    rw [inv_pow, inv_pow]
    field_simp [positive.ne', lengthPositive.ne', frequencyPositive.ne']
  rw [productFormula] at multiplied
  have lowerSq : lower ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg lower]
  have scaledLowerSq : lower ^ 2 * length⁻¹ ^ 2 ≤ (1 / 4) * length⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_right lowerSq (sq_nonneg length⁻¹)
  have finalBound : 3 + (3 / 4) * (1 + lower ^ 2 / length ^ 2) ≤
      uniformInnerLiftSquaredConstant length := by
    unfold uniformInnerLiftSquaredConstant
    have divRewrite : lower ^ 2 / length ^ 2 = lower ^ 2 * length⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    rw [divRewrite]
    nlinarith [sq_nonneg length⁻¹]
  exact comparison.trans (multiplied.trans finalBound)

theorem uniformInnerLiftMode_energy_sq (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (uniformInnerLiftMode lower mode vector)‖ ^ 2 ≤
      uniformInnerLiftSquaredConstant length * ‖vector‖ ^ 2 := by
  have lowerOne : lower ≤ 1 := lowerHalf.trans (by norm_num)
  have literal := annularModeEnergyCore_norm_sq lower length positive lowerOne mode.val.1 mode.val.2
    (uniformInnerLiftMode lower mode vector)
  rw [uniformInnerLiftMode_outer, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at literal
  have factorization : (∫ radius in lower..1,
      radius * (‖(uniformInnerLiftMode lower mode vector).val.2 radius‖ ^ 2 +
        annularPotential length radius mode.val.1 mode.val.2 *
          ‖(uniformInnerLiftMode lower mode vector).val.1 radius‖ ^ 2)) =
      (∫ radius in lower..1, radius *
        (deriv (uniformInnerLiftProfile lower mode) radius ^ 2 +
          annularPotential length radius mode.val.1 mode.val.2 *
            uniformInnerLiftProfile lower mode radius ^ 2)) * ‖vector‖ ^ 2 := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro radius _
    change radius * (‖(smoothScalarRadialCore _ _ vector).val.2 radius‖ ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 *
        ‖uniformInnerLiftProfile lower mode radius • vector‖ ^ 2) = _
    rw [smoothScalarRadialCore_slope, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [literal, factorization]
  exact mul_le_mul_of_nonneg_right
    (uniformInnerLiftProfile_energy_integral lower length positive lowerHalf lengthPositive mode)
    (sq_nonneg _)

def uniformInnerLiftConstant (length : ℝ) : ℝ := Real.sqrt (uniformInnerLiftSquaredConstant length)

theorem uniformInnerLiftMode_energy_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (uniformInnerLiftMode lower mode vector)‖ ≤
      uniformInnerLiftConstant length * ‖vector‖ := by
  unfold uniformInnerLiftConstant
  have rooted := Real.sqrt_le_sqrt
    (uniformInnerLiftMode_energy_sq lower length positive lowerHalf lengthPositive mode vector)
  simpa only [Real.sqrt_mul (uniformInnerLiftSquaredConstant_nonnegative length),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using rooted

end Grad.AnnularUniformBoundary
