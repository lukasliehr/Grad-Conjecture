import AEF2CompletedUniformOuterTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.BoundaryLift

/-- First moment of a decaying exponential on any nonnegative interval. -/
theorem exponential_first_moment_le (rate endpoint : ℝ) (ratePositive : 0 < rate)
    (endpointNonnegative : 0 ≤ endpoint) :
    (∫ time in (0 : ℝ)..endpoint, time * Real.exp (-rate * time)) ≤ rate⁻¹ ^ 2 := by
  let primitive : ℝ → ℝ := fun time =>
    -((rate * time + 1) * Real.exp (-rate * time)) / rate ^ 2
  have derivative : ∀ time : ℝ,
      HasDerivAt primitive (time * Real.exp (-rate * time)) time := by
    intro time
    have affine := ((hasDerivAt_id time).const_mul rate).add_const 1
    have exponential := ((hasDerivAt_id time).const_mul (-rate)).exp
    apply (affine.mul exponential).neg.div_const (rate ^ 2) |>.congr_deriv
    simp only [id_eq, mul_one]
    field_simp [ratePositive.ne']
    ring
  have integrandContinuous : Continuous (fun time : ℝ => time * Real.exp (-rate * time)) := by
    fun_prop
  have primitiveContinuous : Continuous primitive := by
    dsimp only [primitive]
    fun_prop
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le endpointNonnegative
    primitiveContinuous.continuousOn
    (fun time _ => derivative time) (integrandContinuous.intervalIntegrable 0 endpoint)
  have terminalNonnegative : 0 ≤ (rate * endpoint + 1) * Real.exp (-rate * endpoint) :=
    mul_nonneg (by nlinarith) (Real.exp_pos _).le
  have primitiveEnd : primitive endpoint ≤ 0 := by
    dsimp only [primitive]
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg terminalNonnegative (sq_nonneg rate))
  have primitiveZero : primitive 0 = -(rate⁻¹ ^ 2) := by
    dsimp only [primitive]
    simp only [mul_zero, zero_add, Real.exp_zero, one_mul]
    field_simp [ratePositive.ne']
  rw [fundamental, primitiveZero]
  calc
    primitive endpoint - -(rate⁻¹ ^ 2) ≤ 0 - -(rate⁻¹ ^ 2) :=
      sub_le_sub_right primitiveEnd _
    _ = rate⁻¹ ^ 2 := by ring

/-- The radial factor in `r dr` cancels the scaled exponential width. -/
theorem shifted_radial_exponential_le (lower rate : ℝ) (positive : 0 < lower)
    (lowerOne : lower ≤ 1) (ratePositive : 0 < rate) :
    (∫ radius in lower..1, radius * Real.exp (-rate * (radius - lower))) ≤
      lower * rate⁻¹ + rate⁻¹ ^ 2 := by
  have endpointNonnegative : 0 ≤ 1 - lower := sub_nonneg.mpr lowerOne
  have translation :
      (∫ radius in lower..1, radius * Real.exp (-rate * (radius - lower))) =
        ∫ time in (0 : ℝ)..(1 - lower),
          (lower + time) * Real.exp (-rate * time) := by
    have translated := intervalIntegral.integral_comp_sub_right
      (fun time : ℝ => (lower + time) * Real.exp (-rate * time))
      (a := lower) (b := 1) lower
    have leftFunctions :
        (fun radius : ℝ => (lower + (radius - lower)) * Real.exp (-rate * (radius - lower))) =
          fun radius => radius * Real.exp (-rate * (radius - lower)) := by
      funext radius
      congr 1
      ring
    rw [leftFunctions] at translated
    simpa only [sub_self] using translated
  rw [translation]
  have expIntegrable : IntervalIntegrable (fun time : ℝ => Real.exp (-rate * time)) volume 0 (1 - lower) :=
    (by fun_prop : Continuous (fun time : ℝ => Real.exp (-rate * time))).intervalIntegrable _ _
  have momentIntegrable : IntervalIntegrable
      (fun time : ℝ => time * Real.exp (-rate * time)) volume 0 (1 - lower) :=
    (by fun_prop : Continuous (fun time : ℝ => time * Real.exp (-rate * time))).intervalIntegrable _ _
  rw [show (fun time : ℝ => (lower + time) * Real.exp (-rate * time)) =
      fun time => lower * Real.exp (-rate * time) + time * Real.exp (-rate * time) by
        funext time; ring,
    intervalIntegral.integral_add (expIntegrable.const_mul lower) momentIntegrable,
    intervalIntegral.integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (exponential_decay_integral_le rate (1 - lower) ratePositive endpointNonnegative) positive.le)
    (exponential_first_moment_le rate (1 - lower) ratePositive endpointNonnegative)

end Grad.AnnularUniformBoundary
