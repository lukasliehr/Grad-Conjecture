import AIV3LiteralInverseProductRule

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph Grad.AnnularHighTilt

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)

theorem originalFluxTilt_inverse_bound
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖(originalFluxTiltEquivalence lower length positive bounded lengthPositive).symm field‖ ≤
      (2 + length⁻¹ + highTiltExponent) * ‖field‖ := by
  let output := (originalFluxTiltEquivalence lower length positive bounded lengthPositive).symm field
  have inputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  have outputSq := originalNuGraph_norm_sq lower positive output
  have value : ‖field.val 0‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 0), sq_nonneg ‖field.val 1‖]
  have slope : ‖field.val 1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 1), sq_nonneg ‖field.val 0‖]
  have outValue : ‖output.val 0‖ ≤ ‖field‖ :=
    (highBulkUnweight_bound lower positive bounded _).trans value
  have outSlope : ‖output.val 1‖ ≤ (1 + length⁻¹ + highTiltExponent) * ‖field‖ := by
    rw [originalFluxTilt_inverse_slope]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ (1 + length⁻¹) * ‖field.val 1‖ + highTiltExponent * ‖field.val 0‖ :=
        add_le_add (originalUnweightSlope_bound lower length positive lengthPositive _)
          (originalUnweightValueSlope_bound lower positive _)
      _ ≤ (1 + length⁻¹) * ‖field‖ + highTiltExponent * ‖field‖ :=
        add_le_add (mul_le_mul_of_nonneg_left slope (by positivity))
          (mul_le_mul_of_nonneg_left value highTiltExponent_pos.le)
      _ = _ := by ring
  have outSum : ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := by
    nlinarith [norm_nonneg output, norm_nonneg (output.val 0), norm_nonneg (output.val 1),
      mul_nonneg (norm_nonneg (output.val 0)) (norm_nonneg (output.val 1))]
  calc
    _ ≤ ‖output.val 0‖ + ‖output.val 1‖ := outSum
    _ ≤ ‖field‖ + (1 + length⁻¹ + highTiltExponent) * ‖field‖ := add_le_add outValue outSlope
    _ = _ := by ring

theorem originalNuOmegaEquivalence_bound (field : originalNuGraph lower positive) :
    ‖originalNuOmegaEquivalence lower length positive lengthPositive field‖ ≤
      (3 + length) * ‖field‖ := by
  let output := originalNuOmegaEquivalence lower length positive lengthPositive field
  have inputSq := originalNuGraph_norm_sq lower positive field
  have outputSq := annularOmegaGraph_norm_sq lower length positive lengthPositive output
  have value : ‖field.val 0‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 0), sq_nonneg ‖field.val 1‖]
  have slope : ‖field.val 1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg (field.val 1), sq_nonneg ‖field.val 0‖]
  have outValue : ‖output.val 0‖ ≤ ‖field‖ := value
  have outSlope : ‖output.val 1‖ ≤ (2 + length) * ‖field‖ := by
    change ‖annularNuToOmega lower length positive lengthPositive (field.val 1)‖ ≤ _
    exact (annularScalarFamily_bound _ _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left slope (by positivity))
  have outSum : ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := by
    nlinarith [norm_nonneg output, norm_nonneg (output.val 0), norm_nonneg (output.val 1),
      mul_nonneg (norm_nonneg (output.val 0)) (norm_nonneg (output.val 1))]
  calc
    _ ≤ ‖output.val 0‖ + ‖output.val 1‖ := outSum
    _ ≤ ‖field‖ + (2 + length) * ‖field‖ := add_le_add outValue outSlope
    _ = _ := by ring

theorem originalFluxTilt_forward_bound (field : originalNuGraph lower positive) :
    ‖originalFluxTiltEquivalence lower length positive bounded lengthPositive field‖ ≤
      (3 * (3 + length) * lower ^ (-highTiltExponent)) * ‖field‖ := by
  change ‖highOmegaWeight lower length positive bounded lengthPositive
    (originalNuOmegaEquivalence lower length positive lengthPositive field)‖ ≤ _
  apply (highOmegaWeight_bound lower length positive bounded lengthPositive _).trans
  calc
    _ ≤ (3 * lower ^ (-highTiltExponent)) * ((3 + length) * ‖field‖) :=
      mul_le_mul_of_nonneg_left (originalNuOmegaEquivalence_bound lower length positive lengthPositive field)
        (by positivity)
    _ = _ := by ring

end Grad.AnnularOriginalHigh
