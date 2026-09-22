import AIV2UniformCombinedNuMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.SourceCollarDivision

private theorem scalarRadialMap_product (lower : ℝ) (first second result : C(ℝ, ℝ))
    (firstBound secondBound resultBound : ℝ)
    (firstLaw : ∀ r ∈ Icc lower 1, |first r| ≤ firstBound)
    (secondLaw : ∀ r ∈ Icc lower 1, |second r| ≤ secondBound)
    (resultLaw : ∀ r ∈ Icc lower 1, |result r| ≤ resultBound)
    (product : ∀ r, first r * second r = result r) (field : RadialL2 1 lower) :
    scalarRadialMap lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field) =
    scalarRadialMap lower result resultBound resultLaw field := by
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field),
    scalarRadialMap_ae lower second secondBound secondLaw field,
    scalarRadialMap_ae lower result resultBound resultLaw field] with radius outer inner resultEq
  rw [outer, inner, resultEq, smul_smul, product]

theorem omegaToNu_unweight_bulk (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (field : AnnularBulk lower) :
    annularOmegaToNu lower length positive lengthPositive
      (highBulkUnweight lower positive bounded field) =
    originalUnweightSlope lower length positive lengthPositive field := by
  apply lp.ext
  funext mode
  apply scalarRadialMap_product lower
    (annularOmegaOverNuCurve lower length positive mode)
    (highPowerCurve lower highTiltExponent positive)
    (originalUnweightSlopeCurve lower length positive mode)
    ((1 + length⁻¹) / lower) 1 (1 + length⁻¹)
    (annularOmegaOverNu_bound lower length positive lengthPositive mode)
    (highPositivePower_bound lower positive bounded)
    (originalUnweightSlopeCurve_bound lower length positive lengthPositive mode)
  intro radius
  change annularOmegaOverNuCurve lower length positive mode radius *
    highPowerCurve lower highTiltExponent positive radius =
    highPowerCurve lower highTiltExponent positive radius *
      annularOmegaOverNuCurve lower length positive mode radius
  exact mul_comm _ _

theorem omegaToNu_unweight_product (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (field : AnnularBulk lower) :
    annularOmegaToNu lower length positive lengthPositive
      (highOmegaUnweightSlopeTerm lower length positive bounded field) =
    originalUnweightValueSlope lower positive field := by
  apply lp.ext
  funext mode
  apply scalarRadialMap_product lower
    (annularOmegaOverNuCurve lower length positive mode)
    (highOmegaSlopeRatio lower length highTiltExponent positive mode)
    (originalUnweightValueSlopeCurve lower positive mode)
    ((1 + length⁻¹) / lower) (highTiltExponent / 3) highTiltExponent
    (annularOmegaOverNu_bound lower length positive lengthPositive mode)
    (highOmegaPositiveSlope_bound lower length positive bounded mode)
    (originalUnweightValueSlopeCurve_bound lower positive mode)
  intro radius
  change (annularOmegaCurve lower length positive mode radius /
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) *
    (highPowerSlopeCurve lower highTiltExponent positive radius /
      annularOmegaCurve lower length positive mode radius) =
    highPowerSlopeCurve lower highTiltExponent positive radius /
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  field_simp [(annularOmegaCurve_pos lower length positive mode radius).ne']

/-- Actual inverse between the original nu graph and BF omega graph. -/
def originalFluxTiltEquivalence (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) :
    originalNuGraph lower positive ≃L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  (originalNuOmegaEquivalence lower length positive lengthPositive).trans
    (highOmegaTiltEquivalence lower length positive bounded lengthPositive)

theorem originalFluxTilt_value (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (field : originalNuGraph lower positive) :
    (originalFluxTiltEquivalence lower length positive bounded lengthPositive field).val 0 =
      highBulkWeight lower positive bounded (field.val 0) := rfl

theorem originalFluxTilt_inverse_value (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ((originalFluxTiltEquivalence lower length positive bounded lengthPositive).symm field).val 0 =
      highBulkUnweight lower positive bounded (field.val 0) := rfl

/-- BOTH inverse derivative terms are retained, on the genuine closed graph. -/
theorem originalFluxTilt_inverse_slope (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ((originalFluxTiltEquivalence lower length positive bounded lengthPositive).symm field).val 1 =
      originalUnweightSlope lower length positive lengthPositive (field.val 1) +
        originalUnweightValueSlope lower positive (field.val 0) := by
  change annularOmegaToNu lower length positive lengthPositive
    (highBulkUnweight lower positive bounded (field.val 1) +
      highOmegaUnweightSlopeTerm lower length positive bounded (field.val 0)) = _
  rw [map_add, omegaToNu_unweight_bulk, omegaToNu_unweight_product]

end Grad.AnnularOriginalHigh
