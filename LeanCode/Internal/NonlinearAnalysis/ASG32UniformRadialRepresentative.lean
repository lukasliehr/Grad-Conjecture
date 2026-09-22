import ASG31ActualCompactSourceConsumer

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev RadialContinuousSection (dimension : ℕ) (lower : ℝ) :=
  C(Icc lower (1 : ℝ), ComplexEuclidean dimension)

def smoothRadialSection (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] RadialContinuousSection dimension lower where
  toFun core := ⟨fun radius => core.val.val.1 radius.val, core.val.val.1.continuous.comp continuous_subtype_val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothRadial_point_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (core : SmoothRadialCore dimension)
    (radius : Icc lower (1 : ℝ)) :
    ‖core.val.val.1 radius.val‖ ≤ sourceEndpointConstant lower * ‖weightedRadialCore dimension lower core‖ := by
  have value := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.1
  have slope := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.2
  have terminal := scalar_collar_trace core.val.val.1 core.val.val.2 lower 1 bounded le_rfl
    core.val.val.1.continuous core.val.val.2.continuous (fun point _ => core.val.property point)
  simp only [one_mul, inv_one] at terminal
  have initial := initial_endpoint_energy_bound core.val.val.1 core.val.val.2 radius.val 1 radius.property.2
    core.val.val.1.continuous core.val.val.2.continuous (fun point _ => core.val.property point)
  have valueLe := squareIntegral_mono core.val.val.1 core.val.val.1.continuous radius.property.1 radius.property.2 le_rfl
  have slopeLe := squareIntegral_mono core.val.val.2 core.val.val.2.continuous radius.property.1 radius.property.2 le_rfl
  have unweighted : ‖core.val.val.1 radius.val‖ ^ 2 ≤ (collarTraceConstant lower + 1) *
      ((∫ point in lower..1, ‖core.val.val.1 point‖ ^ 2) +
        (∫ point in lower..1, ‖core.val.val.2 point‖ ^ 2)) := by nlinarith
  have constantNonnegative : 0 ≤ collarTraceConstant lower + 1 := by
    have := collarTraceConstant_one_le bounded
    linarith
  have storage : ‖weightedRadialCore dimension lower core‖ ^ 2 =
      ‖weightedCurveLinear dimension lower core.val.val.1‖ ^ 2 +
        ‖weightedCurveLinear dimension lower core.val.val.2‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    rfl
  have squared : lower * ‖core.val.val.1 radius.val‖ ^ 2 ≤
      (collarTraceConstant lower + 1) * ‖weightedRadialCore dimension lower core‖ ^ 2 := by
    rw [storage]
    calc
      _ ≤ lower * ((collarTraceConstant lower + 1) *
          ((∫ point in lower..1, ‖core.val.val.1 point‖ ^ 2) +
            (∫ point in lower..1, ‖core.val.val.2 point‖ ^ 2))) := mul_le_mul_of_nonneg_left unweighted positive.le
      _ = (collarTraceConstant lower + 1) *
          (lower * (∫ point in lower..1, ‖core.val.val.1 point‖ ^ 2) +
            lower * (∫ point in lower..1, ‖core.val.val.2 point‖ ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add value slope) constantNonnegative
  have divided : ‖core.val.val.1 radius.val‖ ^ 2 ≤
      ((collarTraceConstant lower + 1) / lower) * ‖weightedRadialCore dimension lower core‖ ^ 2 := by
    calc
      _ ≤ ((collarTraceConstant lower + 1) * ‖weightedRadialCore dimension lower core‖ ^ 2) / lower :=
        (le_div_iff₀ positive).2 (by nlinarith [squared])
      _ = _ := by ring
  have rooted := Real.sqrt_le_sqrt divided
  simpa only [sourceEndpointConstant, Real.sqrt_mul (div_nonneg constantNonnegative positive.le),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using rooted

theorem smoothRadialSection_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (core : SmoothRadialCore dimension) :
    ‖smoothRadialSection dimension lower core‖ ≤
      sourceEndpointConstant lower * ‖weightedRadialCore dimension lower core‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
  exact smoothRadial_point_bound dimension lower positive bounded core

end Grad.AnnularSourceGraph
