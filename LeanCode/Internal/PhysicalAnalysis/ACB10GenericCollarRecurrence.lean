import ACB9LiteralCenterCollarEquation
import AOD4IntegratedRadialRecurrence

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.CircularHighRegularity

private theorem center_integrate_radial_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (positive : 0 ≤ lower) (bounded : lower < 1)
    (value forcing : ℝ → E) (valueSmooth : ContDiffOn ℝ ∞ value (Icc lower 1))
    (forcingSmooth : ContDiffOn ℝ ∞ forcing (Icc lower 1)) (order : ℕ) (constant ceiling : ℝ)
    (bound : ∀ radius ∈ Icc lower 1,
      ‖iteratedDerivWithin (order + 2) value (Icc lower 1) radius‖ ^ 2 ≤
        4 * (constant * (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index + 1) value (Icc lower 1) radius‖ ^ 2) +
          constant * (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2) +
          ceiling ^ 2 * ‖iteratedDerivWithin order value (Icc lower 1) radius‖ ^ 2 +
          ‖iteratedDerivWithin order forcing (Icc lower 1) radius‖ ^ 2)) :
    radialWithinEnergy lower (order + 2) value ≤
      4 * (constant * (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index + 1) value) +
        constant * (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index) value) +
        ceiling ^ 2 * radialWithinEnergy lower order value + radialWithinEnergy lower order forcing) := by
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
  have totalI := (((firstI.const_mul constant).add (secondI.const_mul (constant))).add
    ((valueI order).const_mul (ceiling ^ 2))).add forcingI
  have integral := intervalIntegral.integral_mono_on bounded.le (valueI (order + 2)) (totalI.const_mul 4)
    (fun radius inside => by
      have pointwise := mul_le_mul_of_nonneg_left (bound radius inside) (positive.trans inside.1)
      exact pointwise.trans_eq (by
        simp only [Finset.sum_apply, density, forcingDensity]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (((firstI.const_mul constant).add (secondI.const_mul (constant))).add
      ((valueI order).const_mul (ceiling ^ 2))) forcingI,
    intervalIntegral.integral_add ((firstI.const_mul constant).add (secondI.const_mul (constant)))
      ((valueI order).const_mul (ceiling ^ 2)),
    intervalIntegral.integral_add (firstI.const_mul constant) (secondI.const_mul (constant)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at integral
  simp only [Finset.sum_apply] at integral
  rw [intervalIntegral.integral_finsetSum (fun index _ => valueI (order - index + 1)),
    intervalIntegral.integral_finsetSum (fun index _ => valueI (order - index))] at integral
  exact integral


/-- A generic genuine ODE recurrence on the fixed positive collar. The
coefficient bound is independent of the forcing and the smooth solution. -/
theorem centerODE_energy_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value forcing : ℝ → E) (valueSmooth : ContDiffOn ℝ ∞ value (Icc lower 1))
    (forcingSmooth : ContDiffOn ℝ ∞ forcing (Icc lower 1)) (scalar ceiling : ℝ)
    (scalarBound : |scalar| ≤ ceiling)
    (equation : EqOn (derivWithin (derivWithin value (Icc lower 1)) (Icc lower 1))
      (fun radius => -(radius⁻¹ • derivWithin value (Icc lower 1) radius) +
        radius⁻¹ ^ 2 • value radius + scalar • value radius - forcing radius) (Icc lower 1))
    (order : ℕ) :
    radialWithinEnergy lower (order + 2) value ≤
      4 * (radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index + 1) value) +
        radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index) value) +
        ceiling ^ 2 * radialWithinEnergy lower order value + radialWithinEnergy lower order forcing) := by
  apply center_integrate_radial_recurrence lower positive.le bounded value forcing valueSmooth forcingSmooth order
    (radialProductConstant lower positive bounded order) ceiling
  intro radius inside
  have reciprocalSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun point member => (positive.trans_le member.1).ne')
  have differentiated := differentiated_radial_equation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    value forcing (fun radius : ℝ => radius⁻¹) (fun radius : ℝ => radius⁻¹ ^ 2) 1 scalar
    valueSmooth forcingSmooth reciprocalSmooth (reciprocalSmooth.pow 2) (by simpa only [one_smul] using equation)
    order radius inside
  rw [one_smul] at differentiated
  let first := radialLeibniz order (fun radius : ℝ => radius⁻¹)
    (derivWithin value (Icc lower 1)) (Icc lower 1) radius
  let second := radialLeibniz order (fun radius : ℝ => radius⁻¹ ^ 2) value (Icc lower 1) radius
  have firstBound : ‖first‖ ^ 2 ≤ radialProductConstant lower positive bounded order *
      ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index + 1) value (Icc lower 1) radius‖ ^ 2 := by
    have estimate := radialLeibniz_norm_sq order (fun radius : ℝ => radius⁻¹)
      (derivWithin value (Icc lower 1)) (Icc lower 1) radius (reciprocalJetBound lower positive bounded order)
      (fun index upper => (reciprocalJet_bound lower positive bounded order index upper radius inside).1)
    simpa only [first, radialProductConstant, iteratedDerivWithin_succ'] using estimate
  have secondBound : ‖second‖ ^ 2 ≤ radialProductConstant lower positive bounded order *
      ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2 :=
    radialLeibniz_norm_sq order (fun radius : ℝ => radius⁻¹ ^ 2) value (Icc lower 1) radius
      (reciprocalJetBound lower positive bounded order)
      (fun index upper => (reciprocalJet_bound lower positive bounded order index upper radius inside).2)
  have scalarSquare : scalar ^ 2 ≤ ceiling ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg scalar) scalarBound 2
  have four := norm_four_sq (-first) second
    (scalar • iteratedDerivWithin order value (Icc lower 1) radius)
    (-iteratedDerivWithin order forcing (Icc lower 1) radius)
  simp only [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at four
  rw [differentiated]
  simpa only [first, second, sub_eq_add_neg] using four.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add firstBound secondBound)
      (mul_le_mul_of_nonneg_right scalarSquare (sq_nonneg _))) le_rfl) (by norm_num))

end Grad.ActualCenterBounds
