import GC20TraceWindow

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

theorem squareIntegral_mono {Value : Type*} [NormedAddCommGroup Value]
    (curve : ℝ → Value) (continuousCurve : Continuous curve) {a b c d : ℝ}
    (left : a ≤ b) (middle : b ≤ c) (right : c ≤ d) :
    (∫ time in b..c, ‖curve time‖ ^ 2) ≤ ∫ time in a..d, ‖curve time‖ ^ 2 := by
  apply intervalIntegral.integral_mono_interval left middle right
  · filter_upwards with time
    exact sq_nonneg _
  · exact (continuousCurve.norm.pow 2).intervalIntegrable a d

/-- The frequency-normalized collar inequality, proved on the actual
smooth core by the terminal interval min(1-a,1/nu), FTC and averaging. -/
theorem scalar_collar_trace {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] (curve derivative : ℝ → Value) (lower frequency : ℝ)
    (lowerOne : lower < 1) (oneLe : 1 ≤ frequency)
    (curveContinuous : Continuous curve) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo lower 1, HasDerivAt curve (derivative time) time) :
    ‖curve 1‖ ^ 2 ≤ collarTraceConstant lower *
      (frequency * (∫ time in lower..1, ‖curve time‖ ^ 2) +
        frequency⁻¹ * (∫ time in lower..1, ‖derivative time‖ ^ 2)) := by
  let window := traceWindow lower frequency
  let start := 1 - window
  let base := ∫ time in lower..1, ‖curve time‖ ^ 2
  let slope := ∫ time in lower..1, ‖derivative time‖ ^ 2
  let energy := frequency * base + frequency⁻¹ * slope
  have positive : 0 < frequency := zero_lt_one.trans_le oneLe
  have windowPositive : 0 < window := traceWindow_pos lowerOne positive
  have lowerStart : lower ≤ start := by
    have := traceWindow_le_length lower frequency
    dsimp [start, window]
    linarith
  have startOne : start ≤ 1 := by dsimp [start]; linarith
  have baseNonnegative : 0 ≤ base := intervalIntegral.integral_nonneg lowerOne.le (fun _ _ => sq_nonneg _)
  have slopeNonnegative : 0 ≤ slope := intervalIntegral.integral_nonneg lowerOne.le (fun _ _ => sq_nonneg _)
  have sample (time : ℝ) (inside : time ∈ Icc start 1) : ‖curve 1‖ ^ 2 ≤ ‖curve time‖ ^ 2 + energy := by
    have lowerTime := lowerStart.trans inside.1
    have preliminary := endpoint_energy_bound curve derivative time 1 frequency inside.2 positive
      curveContinuous derivativeContinuous (fun point membership => differentiates point
        ⟨lt_of_le_of_lt lowerTime membership.1, membership.2⟩)
    have baseBound := squareIntegral_mono curve curveContinuous lowerTime inside.2 le_rfl
    have slopeBound := squareIntegral_mono derivative derivativeContinuous lowerTime inside.2 le_rfl
    have bound := preliminary.trans (add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left baseBound positive.le))
      (mul_le_mul_of_nonneg_left slopeBound (inv_pos.mpr positive).le))
    simpa only [energy, base, slope, add_assoc] using bound
  have average := intervalIntegral.integral_mono_on (μ := volume) startOne
    (continuous_const.intervalIntegrable start 1)
    (((curveContinuous.norm.pow 2).add continuous_const).intervalIntegrable start 1)
    (fun time inside => sample time inside)
  change (∫ time in start..1, ‖curve 1‖ ^ 2) ≤
    ∫ time in start..1, ‖curve time‖ ^ 2 + energy at average
  have integralSum : (∫ time in start..1, ‖curve time‖ ^ 2 + energy) =
      (∫ time in start..1, ‖curve time‖ ^ 2) + (1 - start) * energy := by
    rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const, smul_eq_mul]
    · exact (curveContinuous.norm.pow 2).intervalIntegrable start 1
    · exact continuous_const.intervalIntegrable start 1
  rw [intervalIntegral.integral_const, integralSum] at average
  have length : 1 - start = window := by dsimp [start]; ring
  simp only [smul_eq_mul, length] at average
  have integralBound := squareIntegral_mono curve curveContinuous lowerStart startOne le_rfl
  have aggregate : window * ‖curve 1‖ ^ 2 ≤ base + window * energy :=
    average.trans (add_le_add integralBound le_rfl)
  have divided := mul_le_mul_of_nonneg_left aggregate (inv_pos.mpr windowPositive).le
  have divided' : ‖curve 1‖ ^ 2 ≤ window⁻¹ * base + energy := by
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ windowPositive.ne', one_mul] using divided
  have normalized := divided'.trans (add_le_add
    (mul_le_mul_of_nonneg_right (traceWindow_inverse_bound lowerOne oneLe) baseNonnegative) le_rfl)
  calc
    ‖curve 1‖ ^ 2 ≤ ((1 - lower)⁻¹ + 1) * frequency * base + energy := normalized
    _ = collarTraceConstant lower * (frequency * base) + frequency⁻¹ * slope := by
      dsimp [energy, collarTraceConstant]
      ring
    _ ≤ collarTraceConstant lower * (frequency * base) +
        collarTraceConstant lower * (frequency⁻¹ * slope) :=
      add_le_add le_rfl (le_mul_of_one_le_left (mul_nonneg (inv_pos.mpr positive).le slopeNonnegative)
        (collarTraceConstant_one_le lowerOne))
    _ = _ := by dsimp [base, slope]; ring

end Grad.GaugeCoefficients.Physical.WeightedTrace
