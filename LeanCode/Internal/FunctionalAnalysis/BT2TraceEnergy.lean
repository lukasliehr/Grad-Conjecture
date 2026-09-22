import BT1Boundary
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Grad.BoundaryTrace

theorem frequency_young (frequency first second : ℝ) (positive : 0 < frequency) :
    2 * first * second ≤ frequency * first ^ 2 + frequency⁻¹ * second ^ 2 := by
  apply (mul_le_mul_iff_right₀ positive).mp
  have squared := sq_nonneg (frequency * first - second)
  have cancellation : frequency * frequency⁻¹ = 1 := mul_inv_cancel₀ positive.ne'
  nlinarith [show frequency * (frequency⁻¹ * second ^ 2) = second ^ 2 by
    rw [← mul_assoc, cancellation, one_mul]]

/-- The literal finite-collar fundamental theorem identity in N23.
It applies before Fourier summation, without assuming a completed trace. -/
theorem collar_energy_identity {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] (curve derivative : ℝ → Value) (endpoint : ℝ)
    (endpointNonnegative : 0 ≤ endpoint) (curveContinuous : Continuous curve)
    (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo 0 endpoint, HasDerivAt curve (derivative time) time)
    (vanishes : curve endpoint = 0) :
    ‖curve 0‖ ^ 2 = -2 * ∫ time in 0..endpoint, inner ℝ (curve time) (derivative time) := by
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    endpointNonnegative (curveContinuous.norm.pow 2).continuousOn
    (fun time inside => (differentiates time inside).norm_sq)
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).intervalIntegrable 0 endpoint)
  change (∫ time in 0..endpoint, 2 * inner ℝ (curve time) (derivative time)) =
    ‖curve endpoint‖ ^ 2 - ‖curve 0‖ ^ 2 at fundamental
  rw [vanishes, norm_zero, zero_pow (by decide), zero_sub,
    intervalIntegral.integral_const_mul] at fundamental
  linarith

/-- Frequency-scaled one-sided trace bound. The cutoff will make the far
endpoint zero; frequency is the actual sqrt(1+m²+n²). -/
theorem collar_energy_bound {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] (curve derivative : ℝ → Value) (endpoint frequency : ℝ)
    (endpointNonnegative : 0 ≤ endpoint) (frequencyPositive : 0 < frequency)
    (curveContinuous : Continuous curve) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo 0 endpoint, HasDerivAt curve (derivative time) time)
    (vanishes : curve endpoint = 0) :
    ‖curve 0‖ ^ 2 ≤ frequency * (∫ time in 0..endpoint, ‖curve time‖ ^ 2) +
      frequency⁻¹ * (∫ time in 0..endpoint, ‖derivative time‖ ^ 2) := by
  rw [collar_energy_identity curve derivative endpoint endpointNonnegative curveContinuous
    derivativeContinuous differentiates vanishes]
  have pointwise : ∀ time : ℝ,
      -2 * inner ℝ (curve time) (derivative time) ≤
        frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2 := by
    intro time
    have innerBound := abs_real_inner_le_norm (curve time) (derivative time)
    have innerLower := neg_le_abs (inner ℝ (curve time) (derivative time))
    have young := frequency_young frequency ‖curve time‖ ‖derivative time‖ frequencyPositive
    linarith
  have comparison := intervalIntegral.integral_mono_on (μ := volume) endpointNonnegative
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).intervalIntegrable 0 endpoint)
    (((continuous_const.mul (curveContinuous.norm.pow 2)).add
      (continuous_const.mul (derivativeContinuous.norm.pow 2))).intervalIntegrable 0 endpoint)
    (fun time _ => pointwise time)
  change (∫ time in 0..endpoint, -2 * inner ℝ (curve time) (derivative time)) ≤
    ∫ time in 0..endpoint,
      frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2 at comparison
  have energyIntegral : (∫ time in 0..endpoint,
      frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2) =
      frequency * (∫ time in 0..endpoint, ‖curve time‖ ^ 2) +
        frequency⁻¹ * (∫ time in 0..endpoint, ‖derivative time‖ ^ 2) := by
    rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul]
    · exact (continuous_const.mul (curveContinuous.norm.pow 2)).intervalIntegrable 0 endpoint
    · exact (continuous_const.mul (derivativeContinuous.norm.pow 2)).intervalIntegrable 0 endpoint
  rw [intervalIntegral.integral_const_mul, energyIntegral] at comparison
  exact comparison

end Grad.BoundaryTrace
