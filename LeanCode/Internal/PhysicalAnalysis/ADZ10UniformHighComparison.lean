import ADZ9CompletedCoordinateAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularOmegaGraph

/-- Uniform high Domega estimate for multiplication by `r^(9/4)`. -/
theorem highOmegaUnweight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖highOmegaUnweight lower length positive bounded lengthPositive field‖ ≤ 3 * ‖field‖ := by
  let transformed := highOmegaUnweight lower length positive bounded lengthPositive field
  have inputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  have outputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive transformed
  have inputValue : ‖field.val 0‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 0), sq_nonneg ‖field.val 1‖]
  have inputSlope : ‖field.val 1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 1), sq_nonneg ‖field.val 0‖]
  have valueBound : ‖transformed.val 0‖ ≤ ‖field‖ := by
    change ‖highBulkUnweight lower positive bounded (field.val 0)‖ ≤ ‖field‖
    exact (highBulkUnweight_bound lower positive bounded (field.val 0)).trans inputValue
  have slopeBound : ‖transformed.val 1‖ ≤ 2 * ‖field‖ := by
    change ‖highBulkUnweight lower positive bounded (field.val 1) +
      highOmegaUnweightSlopeTerm lower length positive bounded (field.val 0)‖ ≤ _
    calc
      _ ≤ ‖highBulkUnweight lower positive bounded (field.val 1)‖ +
          ‖highOmegaUnweightSlopeTerm lower length positive bounded (field.val 0)‖ := norm_add_le _ _
      _ ≤ ‖field.val 1‖ + (highTiltExponent / 3) * ‖field.val 0‖ :=
        add_le_add (highBulkUnweight_bound lower positive bounded (field.val 1))
          (highOmegaUnweightSlopeTerm_bound lower length positive bounded (field.val 0))
      _ ≤ ‖field‖ + (highTiltExponent / 3) * ‖field‖ := by
        exact add_le_add inputSlope
          (mul_le_mul_of_nonneg_left inputValue (by norm_num [highTiltExponent]))
      _ ≤ ‖field‖ + 1 * ‖field‖ := by
        gcongr
        norm_num [highTiltExponent]
      _ = 2 * ‖field‖ := by ring
  nlinarith [norm_nonneg transformed, norm_nonneg field, norm_nonneg (transformed.val 0),
    norm_nonneg (transformed.val 1)]

/-- The inverse Domega comparison has exactly the BF radial loss
`lower^(-9/4)`, with a fixed numerical constant. -/
theorem highOmegaWeight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖highOmegaWeight lower length positive bounded lengthPositive field‖ ≤
      (3 * lower ^ (-highTiltExponent)) * ‖field‖ := by
  let transformed := highOmegaWeight lower length positive bounded lengthPositive field
  let scale := lower ^ (-highTiltExponent)
  let target := scale * ‖field‖
  have scaleNonnegative : 0 ≤ scale := (Real.rpow_pos_of_pos positive _).le
  have scaleOne : 1 ≤ scale := highNegativePower_one_le lower positive bounded
  have targetNonnegative : 0 ≤ target := mul_nonneg scaleNonnegative (norm_nonneg field)
  have inputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  have outputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive transformed
  have inputValue : ‖field.val 0‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 0), sq_nonneg ‖field.val 1‖]
  have inputSlope : ‖field.val 1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 1), sq_nonneg ‖field.val 0‖]
  have valueBound : ‖transformed.val 0‖ ≤ target := by
    change ‖highBulkWeight lower positive bounded (field.val 0)‖ ≤ target
    exact (highBulkWeight_bound lower positive bounded (field.val 0)).trans
      (mul_le_mul_of_nonneg_left inputValue scaleNonnegative)
  have slopeBound : ‖transformed.val 1‖ ≤ 2 * target := by
    change ‖highBulkWeight lower positive bounded (field.val 1) +
      highOmegaWeightSlopeTerm lower length positive bounded (field.val 0)‖ ≤ _
    calc
      _ ≤ ‖highBulkWeight lower positive bounded (field.val 1)‖ +
          ‖highOmegaWeightSlopeTerm lower length positive bounded (field.val 0)‖ := norm_add_le _ _
      _ ≤ scale * ‖field.val 1‖ + (highTiltExponent / 3 * scale) * ‖field.val 0‖ :=
        add_le_add (highBulkWeight_bound lower positive bounded (field.val 1))
          (highOmegaWeightSlopeTerm_bound lower length positive bounded (field.val 0))
      _ ≤ scale * ‖field‖ + (highTiltExponent / 3 * scale) * ‖field‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left inputSlope scaleNonnegative)
          (mul_le_mul_of_nonneg_left inputValue
            (mul_nonneg (by norm_num [highTiltExponent]) scaleNonnegative))
      _ ≤ scale * ‖field‖ + scale * ‖field‖ := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
        calc
          highTiltExponent / 3 * scale ≤ 1 * scale :=
            mul_le_mul_of_nonneg_right (by norm_num [highTiltExponent]) scaleNonnegative
          _ = scale := one_mul scale
      _ = 2 * target := by simp only [target]; ring
  have frozenSq : ‖transformed‖ ^ 2 = ‖transformed.val 0‖ ^ 2 + ‖transformed.val 1‖ ^ 2 := outputSq
  have frozen : ‖transformed‖ ≤ 3 * target := by
    nlinarith [norm_nonneg transformed, norm_nonneg (transformed.val 0), norm_nonneg (transformed.val 1)]
  simpa only [transformed, target, scale, mul_assoc] using frozen

/-- Exact raw AAG/ADW high-coordinate prerequisite for the BF tilt.  It keeps
both original Hilbert carriers and records the fixed forward and inverse bounds. -/
theorem rawHighTilt_consumer (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) :
    (∃ equivalence : annularEnergySpace lower length positive ≃L[ℂ]
        annularEnergySpace lower length positive,
      (∀ field, equivalence field = highEnergyWeight lower length positive bounded field) ∧
      (∀ field, equivalence.symm field = highEnergyUnweight lower length positive bounded field) ∧
      (∀ field, ‖equivalence field‖ ≤
        (3 * lower ^ (-highTiltExponent)) * ‖field‖) ∧
      (∀ field, ‖equivalence.symm field‖ ≤ 3 * ‖field‖)) ∧
    (∃ equivalence : annularOmegaGraph lower length positive lengthPositive ≃L[ℂ]
        annularOmegaGraph lower length positive lengthPositive,
      (∀ field, equivalence field = highOmegaWeight lower length positive bounded lengthPositive field) ∧
      (∀ field, equivalence.symm field = highOmegaUnweight lower length positive bounded lengthPositive field) ∧
      (∀ field, ‖equivalence field‖ ≤
        (3 * lower ^ (-highTiltExponent)) * ‖field‖) ∧
      (∀ field, ‖equivalence.symm field‖ ≤ 3 * ‖field‖)) := by
  refine ⟨⟨highEnergyTiltEquivalence lower length positive bounded, ?_, ?_, ?_, ?_⟩,
    ⟨highOmegaTiltEquivalence lower length positive bounded lengthPositive, ?_, ?_, ?_, ?_⟩⟩
  · intro field
    rfl
  · intro field
    rfl
  · exact highEnergyWeight_bound lower length positive bounded
  · exact highEnergyUnweight_bound lower length positive bounded
  · intro field
    rfl
  · intro field
    rfl
  · exact highOmegaWeight_bound lower length positive bounded lengthPositive
  · exact highOmegaUnweight_bound lower length positive bounded lengthPositive

end Grad.AnnularHighTilt
