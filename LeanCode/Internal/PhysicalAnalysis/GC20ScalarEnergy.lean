import BT2TraceEnergy

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

theorem endpoint_energy_bound {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] (curve derivative : ℝ → Value) (left right frequency : ℝ)
    (ordered : left ≤ right) (frequencyPositive : 0 < frequency)
    (curveContinuous : Continuous curve) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo left right, HasDerivAt curve (derivative time) time) :
    ‖curve right‖ ^ 2 ≤ ‖curve left‖ ^ 2 +
      frequency * (∫ time in left..right, ‖curve time‖ ^ 2) +
      frequency⁻¹ * (∫ time in left..right, ‖derivative time‖ ^ 2) := by
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ordered (curveContinuous.norm.pow 2).continuousOn
    (fun time inside => (differentiates time inside).norm_sq)
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).intervalIntegrable left right)
  change (∫ time in left..right, 2 * inner ℝ (curve time) (derivative time)) =
    ‖curve right‖ ^ 2 - ‖curve left‖ ^ 2 at fundamental
  have pointwise (time : ℝ) : 2 * inner ℝ (curve time) (derivative time) ≤
      frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2 := by
    have innerBound := real_inner_le_norm (curve time) (derivative time)
    have young := Grad.BoundaryTrace.frequency_young frequency ‖curve time‖ ‖derivative time‖ frequencyPositive
    linarith
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).intervalIntegrable left right)
    (((continuous_const.mul (curveContinuous.norm.pow 2)).add
      (continuous_const.mul (derivativeContinuous.norm.pow 2))).intervalIntegrable left right)
    (fun time _ => pointwise time)
  change (∫ time in left..right, 2 * inner ℝ (curve time) (derivative time)) ≤
    ∫ time in left..right,
      frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2 at comparison
  have energyIntegral : (∫ time in left..right,
      frequency * ‖curve time‖ ^ 2 + frequency⁻¹ * ‖derivative time‖ ^ 2) =
      frequency * (∫ time in left..right, ‖curve time‖ ^ 2) +
        frequency⁻¹ * (∫ time in left..right, ‖derivative time‖ ^ 2) := by
    rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul]
    · exact (continuous_const.mul (curveContinuous.norm.pow 2)).intervalIntegrable left right
    · exact (continuous_const.mul (derivativeContinuous.norm.pow 2)).intervalIntegrable left right
  rw [fundamental, energyIntegral] at comparison
  linarith

end Grad.GaugeCoefficients.Physical.WeightedTrace
