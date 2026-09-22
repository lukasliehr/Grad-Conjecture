import ASG1WeightedRadialCompletion

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The initial-endpoint companion of the accepted terminal energy bound,
from the same genuine derivative and the fundamental theorem of calculus. -/
theorem initial_endpoint_energy_bound {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] (curve derivative : ℝ → Value) (left right : ℝ)
    (ordered : left ≤ right) (curveContinuous : Continuous curve)
    (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ time ∈ Ioo left right, HasDerivAt curve (derivative time) time) :
    ‖curve left‖ ^ 2 ≤ ‖curve right‖ ^ 2 +
      (∫ time in left..right, ‖curve time‖ ^ 2) +
      (∫ time in left..right, ‖derivative time‖ ^ 2) := by
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ordered (curveContinuous.norm.pow 2).neg.continuousOn
    (fun time inside => (differentiates time inside).norm_sq.neg)
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).neg.intervalIntegrable left right)
  change (∫ time in left..right, -(2 * inner ℝ (curve time) (derivative time))) =
    -‖curve right‖ ^ 2 - -‖curve left‖ ^ 2 at fundamental
  have pointwise (time : ℝ) : -(2 * inner ℝ (curve time) (derivative time)) ≤
      ‖curve time‖ ^ 2 + ‖derivative time‖ ^ 2 := by
    have innerBound := real_inner_le_norm (curve time) (-derivative time)
    simp only [inner_neg_right, norm_neg] at innerBound
    have young := Grad.BoundaryTrace.frequency_young 1 ‖curve time‖ ‖derivative time‖ (by norm_num)
    norm_num only [one_mul, inv_one] at young
    linarith
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered
    ((continuous_const.mul (curveContinuous.inner derivativeContinuous)).neg.intervalIntegrable left right)
    (((curveContinuous.norm.pow 2).add (derivativeContinuous.norm.pow 2)).intervalIntegrable left right)
    (fun time _ => pointwise time)
  change (∫ time in left..right, -(2 * inner ℝ (curve time) (derivative time))) ≤
    ∫ time in left..right, ‖curve time‖ ^ 2 + ‖derivative time‖ ^ 2 at comparison
  rw [fundamental] at comparison
  have sum := intervalIntegral.integral_add (μ := volume)
    (f := fun time => ‖curve time‖ ^ 2) (g := fun time => ‖derivative time‖ ^ 2)
    ((curveContinuous.norm.pow 2).intervalIntegrable left right)
    ((derivativeContinuous.norm.pow 2).intervalIntegrable left right)
  rw [sum] at comparison
  linarith

def radialEndpointRadius (lower : ℝ) (endpoint : Fin 2) : ℝ :=
  if endpoint = 0 then lower else 1

def smoothRadialEndpoint (dimension : ℕ) (lower : ℝ) (endpoint : Fin 2) :
    SmoothRadialCore dimension →ₗ[ℝ] ComplexEuclidean dimension where
  toFun core := core.val.val.1 (radialEndpointRadius lower endpoint)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothRadialEndpoint_bound_sq (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (core : SmoothRadialCore dimension) :
    lower * ‖smoothRadialEndpoint dimension lower endpoint core‖ ^ 2 ≤
      (collarTraceConstant lower + 1) * ‖weightedRadialCore dimension lower core‖ ^ 2 := by
  have value := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.1
  have slope := weightedCurve_energy_lower dimension lower positive bounded.le core.val.val.2
  have terminal := scalar_collar_trace core.val.val.1 core.val.val.2 lower 1 bounded le_rfl
    core.val.val.1.continuous core.val.val.2.continuous (fun radius _ => core.val.property radius)
  simp only [one_mul, inv_one] at terminal
  have constantNonnegative : 0 ≤ collarTraceConstant lower :=
    zero_le_one.trans (collarTraceConstant_one_le bounded)
  have storage : ‖weightedRadialCore dimension lower core‖ ^ 2 =
      ‖weightedCurveLinear dimension lower core.val.val.1‖ ^ 2 +
      ‖weightedCurveLinear dimension lower core.val.val.2‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    rfl
  rw [storage]
  have combined := add_le_add value slope
  fin_cases endpoint
  · have initial := initial_endpoint_energy_bound core.val.val.1 core.val.val.2 lower 1 bounded.le
      core.val.val.1.continuous core.val.val.2.continuous (fun radius _ => core.val.property radius)
    change lower * ‖core.val.val.1 lower‖ ^ 2 ≤ _
    have unweighted : ‖core.val.val.1 lower‖ ^ 2 ≤ (collarTraceConstant lower + 1) *
        ((∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
          (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2)) := by nlinarith
    calc
      _ ≤ lower * ((collarTraceConstant lower + 1) *
          ((∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
            (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left unweighted positive.le
      _ = (collarTraceConstant lower + 1) *
          (lower * (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
            lower * (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left combined (by positivity)
  · change lower * ‖core.val.val.1 1‖ ^ 2 ≤ _
    have weighted := weightedEndpointCore_bound dimension lower positive bounded core.val
    change lower * ‖core.val.val.1 1‖ ^ 2 ≤
      collarTraceConstant lower *
        (‖weightedCurveLinear dimension lower core.val.val.1‖ ^ 2 +
          ‖weightedCurveLinear dimension lower core.val.val.2‖ ^ 2) at weighted
    exact weighted.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

def sourceEndpointConstant (lower : ℝ) : ℝ :=
  Real.sqrt ((collarTraceConstant lower + 1) / lower)

theorem smoothRadialEndpoint_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (core : SmoothRadialCore dimension) :
    ‖smoothRadialEndpoint dimension lower endpoint core‖ ≤
      sourceEndpointConstant lower * ‖weightedRadialCore dimension lower core‖ := by
  have squared := smoothRadialEndpoint_bound_sq dimension lower positive bounded endpoint core
  have divided : ‖smoothRadialEndpoint dimension lower endpoint core‖ ^ 2 ≤
      ((collarTraceConstant lower + 1) / lower) * ‖weightedRadialCore dimension lower core‖ ^ 2 := by
    calc
      _ ≤ ((collarTraceConstant lower + 1) * ‖weightedRadialCore dimension lower core‖ ^ 2) / lower :=
        (le_div_iff₀ positive).2 (by nlinarith [squared])
      _ = _ := by ring
  have nonnegative : 0 ≤ (collarTraceConstant lower + 1) / lower := by
    have := collarTraceConstant_one_le bounded
    positivity
  have rooted := Real.sqrt_le_sqrt divided
  simpa only [sourceEndpointConstant, Real.sqrt_mul nonnegative, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using rooted

end Grad.AnnularSourceGraph
