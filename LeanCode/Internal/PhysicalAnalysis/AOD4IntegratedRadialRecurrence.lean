import AOD3PointwiseRadialEstimate

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

/-- Literal r dr energy of the genuine iterated derivative within the collar. -/
def radialWithinEnergy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (order : ℕ) (value : ℝ → E) : ℝ :=
  ∫ radius in lower..1, radius * ‖iteratedDerivWithin order value (Icc lower 1) radius‖ ^ 2

theorem radialWithinEnergy_nonnegative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (positive : 0 ≤ lower) (bounded : lower ≤ 1) (order : ℕ) (value : ℝ → E) :
    0 ≤ radialWithinEnergy lower order value :=
  intervalIntegral.integral_nonneg bounded (fun _ inside =>
    mul_nonneg (positive.trans inside.1) (sq_nonneg _))

theorem radialWithinEnergy_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (bounded : lower < 1) (order : ℕ) (value : ℝ → E)
    (smooth : ContDiffOn ℝ ∞ value (Icc lower 1)) :
    IntervalIntegrable (fun radius => radius * ‖iteratedDerivWithin order value (Icc lower 1) radius‖ ^ 2) volume lower 1 := by
  have finite : (order : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)
  exact ContinuousOn.intervalIntegrable_of_Icc bounded.le
    (continuousOn_id.mul ((smooth.continuousOn_iteratedDerivWithin finite (uniqueDiffOn_Icc bounded)).norm.pow 2))

private theorem integrate_radial_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (positive : 0 ≤ lower) (bounded : lower < 1)
    (value forcing : ℝ → E) (valueSmooth : ContDiffOn ℝ ∞ value (Icc lower 1))
    (forcingSmooth : ContDiffOn ℝ ∞ forcing (Icc lower 1)) (order : ℕ) (constant mode ceiling : ℝ)
    (bound : ∀ radius ∈ Icc lower 1,
      ‖iteratedDerivWithin (order + 2) value (Icc lower 1) radius‖ ^ 2 ≤
        4 * (constant * (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index + 1) value (Icc lower 1) radius‖ ^ 2) +
          mode ^ 4 * constant * (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2) +
          ceiling ^ 4 * ‖iteratedDerivWithin order value (Icc lower 1) radius‖ ^ 2 +
          ‖iteratedDerivWithin order forcing (Icc lower 1) radius‖ ^ 2)) :
    radialWithinEnergy lower (order + 2) value ≤
      4 * (constant * (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index + 1) value) +
        mode ^ 4 * constant * (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index) value) +
        ceiling ^ 4 * radialWithinEnergy lower order value + radialWithinEnergy lower order forcing) := by
  let density (order : ℕ) (radius : ℝ) : ℝ := radius * ‖iteratedDerivWithin order value (Icc lower 1) radius‖ ^ 2
  let forcingDensity (radius : ℝ) : ℝ := radius * ‖iteratedDerivWithin order forcing (Icc lower 1) radius‖ ^ 2
  have valueI (order : ℕ) : IntervalIntegrable (density order) volume lower 1 :=
    radialWithinEnergy_integrable lower bounded order value valueSmooth
  have forcingI : IntervalIntegrable forcingDensity volume lower 1 :=
    radialWithinEnergy_integrable lower bounded order forcing forcingSmooth
  have firstI := IntervalIntegrable.sum (s := Finset.range (order + 1))
    (fun index _ => valueI (order - index + 1))
  have secondI := IntervalIntegrable.sum (s := Finset.range (order + 1))
    (fun index _ => valueI (order - index))
  have totalI := (((firstI.const_mul constant).add (secondI.const_mul (mode ^ 4 * constant))).add
    ((valueI order).const_mul (ceiling ^ 4))).add forcingI
  have integral := intervalIntegral.integral_mono_on bounded.le (valueI (order + 2)) (totalI.const_mul 4)
    (fun radius inside => by
      have pointwise := mul_le_mul_of_nonneg_left (bound radius inside) (positive.trans inside.1)
      exact pointwise.trans_eq (by
        simp only [Finset.sum_apply, density, forcingDensity]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (((firstI.const_mul constant).add (secondI.const_mul (mode ^ 4 * constant))).add
      ((valueI order).const_mul (ceiling ^ 4))) forcingI,
    intervalIntegral.integral_add ((firstI.const_mul constant).add (secondI.const_mul (mode ^ 4 * constant)))
      ((valueI order).const_mul (ceiling ^ 4)),
    intervalIntegral.integral_add (firstI.const_mul constant) (secondI.const_mul (mode ^ 4 * constant)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at integral
  simp only [Finset.sum_apply] at integral
  rw [intervalIntegral.integral_finsetSum (fun index _ => valueI (order - index + 1)),
    intervalIntegral.integral_finsetSum (fun index _ => valueI (order - index))] at integral
  exact integral

/-- Integrated genuine ODE recurrence. Its solution terms all have strictly
smaller radial count; the last term is the actual original Fourier forcing. -/
theorem actualRadial_energy_recurrence (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter ceiling : ℝ) (parameterBound : |parameter| ≤ ceiling)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (order : ℕ) :
    radialWithinEnergy lower (order + 2) (actualRadialValue lower positive bounded mode parameter source) ≤
      4 * (radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index + 1)
          (actualRadialValue lower positive bounded mode parameter source)) +
        (mode : ℝ) ^ 4 * radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index)
          (actualRadialValue lower positive bounded mode parameter source)) +
        ceiling ^ 4 * radialWithinEnergy lower order (actualRadialValue lower positive bounded mode parameter source) +
        radialWithinEnergy lower order (diskCoreRadialCurve mode core)) :=
  integrate_radial_recurrence lower positive.le bounded
    (actualRadialValue lower positive bounded mode parameter source) (diskCoreRadialCurve mode core)
    (weakInverse_closedCollar_smooth lower positive bounded mode high parameter source core same)
    (diskCoreRadialCurve_smooth mode core).contDiffOn order (radialProductConstant lower positive bounded order)
    (mode : ℝ) ceiling
    (actualRadial_jet_pointwise lower positive bounded parameter ceiling parameterBound source core same mode high order)

end Grad.CircularHighRegularity
