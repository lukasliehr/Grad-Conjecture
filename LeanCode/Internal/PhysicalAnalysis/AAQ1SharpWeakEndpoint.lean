import AAT17ExactGradedConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem smoothRadialEndpoint_frequency_bound_sq (dimension : ℕ) (lower frequency : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (oneLe : 1 ≤ frequency)
    (endpoint : Fin 2) (core : SmoothRadialCore dimension) :
    frequency⁻¹ * ‖smoothRadialEndpoint dimension lower endpoint core‖ ^ 2 ≤
      (collarTraceConstant lower / lower) *
        (‖weightedCurveLinear dimension lower core.val.val.1‖ ^ 2 +
          frequency⁻¹ ^ 2 * ‖weightedCurveLinear dimension lower core.val.val.2‖ ^ 2) := by
  have frequencyPositive : 0 < frequency := lt_of_lt_of_le zero_lt_one oneLe
  have trace : ‖smoothRadialEndpoint dimension lower endpoint core‖ ^ 2 ≤
      collarTraceConstant lower *
        (frequency * (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
          frequency⁻¹ * (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2)) := by
    fin_cases endpoint
    · exact scalar_inner_collar_trace _ _ lower frequency bounded oneLe
        core.val.val.1.continuous core.val.val.2.continuous (fun radius _ => core.val.property radius)
    · exact scalar_collar_trace _ _ lower frequency bounded oneLe
        core.val.val.1.continuous core.val.val.2.continuous (fun radius _ => core.val.property radius)
  have value := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.1
  have slope := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.2
  have nonnegative : 0 ≤ collarTraceConstant lower := (collarTraceConstant_one_le bounded).trans' zero_le_one
  calc
    _ ≤ frequency⁻¹ * (collarTraceConstant lower *
        (frequency * (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
          frequency⁻¹ * (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left trace (inv_nonneg.mpr frequencyPositive.le)
    _ = (collarTraceConstant lower / lower) *
        (lower * (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
          frequency⁻¹ ^ 2 * (lower * (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add value (mul_le_mul_of_nonneg_left slope (sq_nonneg _))) (div_nonneg nonnegative positive.le)

/-- The sharp frequency estimate on the original completed weak radial graph.
Both endpoint values are the accepted actual radial traces. -/
theorem weightedRadialTrace_frequency_bound_sq (dimension : ℕ) (lower frequency : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (oneLe : 1 ≤ frequency)
    (endpoint : Fin 2) (field : WeightedRadialH1 dimension lower) :
    frequency⁻¹ * ‖weightedRadialTrace dimension lower positive bounded endpoint field‖ ^ 2 ≤
      (collarTraceConstant lower / lower) *
        (‖weightedRadialCoordinate dimension lower 0 field‖ ^ 2 +
          frequency⁻¹ ^ 2 * ‖weightedRadialCoordinate dimension lower 1 field‖ ^ 2) := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_le (continuous_const.mul
      ((weightedRadialTrace dimension lower positive bounded endpoint).continuous.norm.pow 2))
      (continuous_const.mul (((weightedRadialCoordinate dimension lower 0).continuous.norm.pow 2).add
        (continuous_const.mul ((weightedRadialCoordinate dimension lower 1).continuous.norm.pow 2))))) _ field
  intro core
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply]
  rw [weightedRadialTrace_core, weightedRadialCoordinate_core_zero, weightedRadialCoordinate_core_one]
  exact smoothRadialEndpoint_frequency_bound_sq dimension lower frequency positive bounded oneLe endpoint core

end Grad.AnnularFluxTrace
