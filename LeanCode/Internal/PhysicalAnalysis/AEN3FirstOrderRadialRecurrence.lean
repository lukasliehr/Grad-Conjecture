import AEN2ActualPrimitiveBase

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff BigOperators Interval
namespace Grad.ExceptionalNative
open Grad.CircularHighRegularity

theorem differentiated_firstOrder_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain) (value forcing : ℝ → E)
    (valueSmooth : ContDiffOn ℝ ∞ value domain) (forcingSmooth : ContDiffOn ℝ ∞ forcing domain)
    (coefficient : ℝ → ℝ) (coefficientSmooth : ContDiffOn ℝ ∞ coefficient domain) (scalar : ℝ)
    (equation : EqOn (derivWithin value domain)
      (fun radius => forcing radius + scalar • (coefficient radius • value radius)) domain)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    iteratedDerivWithin (order + 1) value domain radius =
      iteratedDerivWithin order forcing domain radius + scalar • radialLeibniz order coefficient value domain radius := by
  rw [iteratedDerivWithin_succ']
  have transfer := iteratedDerivWithin_congr (n := order) equation inside
  apply transfer.trans
  have forcingN := (contDiffOn_infty.mp forcingSmooth) order
  have productN := (contDiffOn_infty.mp ((coefficientSmooth.smul valueSmooth).const_smul scalar)) order
  change iteratedDerivWithin order (fun radius => forcing radius + scalar • (coefficient • value) radius) domain radius = _
  rw [iteratedDerivWithin_fun_add (n := order) inside unique (forcingN radius inside) (productN radius inside),
    iteratedDerivWithin_fun_const_smul_field]
  have product := iteratedDerivWithin_smul (n := order) inside unique
    ((contDiffOn_infty.mp coefficientSmooth) order radius inside)
    ((contDiffOn_infty.mp valueSmooth) order radius inside)
  rw [product]
  rfl

theorem firstOrder_energy_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value forcing : ℝ → E) (valueSmooth : ContDiffOn ℝ ∞ value (Icc lower 1))
    (forcingSmooth : ContDiffOn ℝ ∞ forcing (Icc lower 1)) (scalar : ℝ) (scalarBound : |scalar| ≤ 2)
    (equation : EqOn (derivWithin value (Icc lower 1))
      (fun radius => forcing radius + scalar • (radius⁻¹ • value radius)) (Icc lower 1)) (order : ℕ) :
    radialWithinEnergy lower (order + 1) value ≤
      4 * (radialWithinEnergy lower order forcing +
        4 * radialProductConstant lower positive bounded order *
          ∑ index ∈ Finset.range (order + 1), radialWithinEnergy lower (order - index) value) := by
  have reciprocalSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun point member => (positive.trans_le member.1).ne')
  have pointwise (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      ‖iteratedDerivWithin (order + 1) value (Icc lower 1) radius‖ ^ 2 ≤
        4 * (‖iteratedDerivWithin order forcing (Icc lower 1) radius‖ ^ 2 +
          4 * radialProductConstant lower positive bounded order *
          ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2) := by
    have productBound := radialLeibniz_norm_sq order (fun radius : ℝ => radius⁻¹) value (Icc lower 1) radius
      (reciprocalJetBound lower positive bounded order)
      (fun index upper => (reciprocalJet_bound lower positive bounded order index upper radius inside).1)
    have scalarSquare : scalar ^ 2 ≤ 4 := by
      have estimate := pow_le_pow_left₀ (abs_nonneg scalar) scalarBound 2
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using estimate
    have productNonnegative : 0 ≤ radialProductConstant lower positive bounded order *
        ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2 :=
      mul_nonneg (radialProductConstant_nonnegative lower positive bounded order)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have scaled := (mul_le_mul_of_nonneg_left productBound (sq_nonneg scalar)).trans
      (mul_le_mul_of_nonneg_right scalarSquare productNonnegative)
    have raw := norm_four_sq (iteratedDerivWithin order forcing (Icc lower 1) radius)
      (scalar • radialLeibniz order (fun radius : ℝ => radius⁻¹) value (Icc lower 1) radius) (0 : E) 0
    simp only [add_zero, norm_zero, zero_pow (by omega : 2 ≠ 0), norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs] at raw
    rw [differentiated_firstOrder_equation (Icc lower 1) (uniqueDiffOn_Icc bounded)
      value forcing valueSmooth forcingSmooth (fun radius : ℝ => radius⁻¹) reciprocalSmooth scalar equation order radius inside]
    exact raw.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (by
      simpa only [radialProductConstant, mul_assoc] using scaled)) (by norm_num))
  let density (count : ℕ) (radius : ℝ) : ℝ := radius * ‖iteratedDerivWithin count value (Icc lower 1) radius‖ ^ 2
  let forcingDensity (radius : ℝ) : ℝ := radius * ‖iteratedDerivWithin order forcing (Icc lower 1) radius‖ ^ 2
  have valueI (count : ℕ) : IntervalIntegrable (density count) volume lower 1 :=
    radialWithinEnergy_integrable lower bounded count value valueSmooth
  have forcingI : IntervalIntegrable forcingDensity volume lower 1 :=
    radialWithinEnergy_integrable lower bounded order forcing forcingSmooth
  have sumI := IntervalIntegrable.sum (s := Finset.range (order + 1)) (fun index _ => valueI (order - index))
  have totalI := forcingI.add (sumI.const_mul (4 * radialProductConstant lower positive bounded order))
  have integrated := intervalIntegral.integral_mono_on bounded.le (valueI (order + 1)) (totalI.const_mul 4)
    (fun radius inside => (mul_le_mul_of_nonneg_left (pointwise radius inside) (positive.le.trans inside.1)).trans_eq (by
      simp only [Finset.sum_apply, density, forcingDensity]
      rw [← Finset.mul_sum]
      ring))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add forcingI
    (sumI.const_mul (4 * radialProductConstant lower positive bounded order)), intervalIntegral.integral_const_mul] at integrated
  simp only [Finset.sum_apply] at integrated
  rw [intervalIntegral.integral_finsetSum (fun index _ => valueI (order - index))] at integrated
  exact integrated

end Grad.ExceptionalNative
