import ADZ3ExactHighOmegaTilt

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem collarPower_inverse_apply (lower power : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (highPowerCurve lower (-power) positive)
      (collarScalar 1 lower (highPowerCurve lower power positive) field) = field := by
  rw [collarScalar_mul_apply]
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower
    (highPowerCurve lower (-power) positive * highPowerCurve lower power positive) field]
    with radius equality
  rw [equality]
  change (highPowerCurve lower (-power) positive radius *
    highPowerCurve lower power positive radius) • field radius = field radius
  rw [highPowerCurve_inverse, one_smul]

private theorem collarOmegaPower_inverse_slope (lower length power : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (value slope : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (highOmegaSlopeRatio lower length (-power) positive mode)
        (collarScalar 1 lower (highPowerCurve lower power positive) value) +
      collarScalar 1 lower (highPowerCurve lower (-power) positive)
        (collarScalar 1 lower (highPowerCurve lower power positive) slope +
          collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value) = slope := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (collarScalar 1 lower (highOmegaSlopeRatio lower length (-power) positive mode)
        (collarScalar 1 lower (highPowerCurve lower power positive) value))
      (collarScalar 1 lower (highPowerCurve lower (-power) positive)
        (collarScalar 1 lower (highPowerCurve lower power positive) slope +
          collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value)),
    collarScalar_ae 1 lower (highOmegaSlopeRatio lower length (-power) positive mode)
      (collarScalar 1 lower (highPowerCurve lower power positive) value),
    collarScalar_ae 1 lower (highPowerCurve lower power positive) value,
    collarScalar_ae 1 lower (highPowerCurve lower (-power) positive)
      (collarScalar 1 lower (highPowerCurve lower power positive) slope +
        collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value),
    Lp.coeFn_add (collarScalar 1 lower (highPowerCurve lower power positive) slope)
      (collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value),
    collarScalar_ae 1 lower (highPowerCurve lower power positive) slope,
    collarScalar_ae 1 lower (highOmegaSlopeRatio lower length power positive mode) value]
    with radius total first powerValue second inner powerSlope ratioValue
  rw [total, Pi.add_apply, first, powerValue, second, inner, Pi.add_apply, powerSlope, ratioValue,
    smul_add, smul_smul, smul_smul, smul_smul]
  have inverse := highPowerCurve_inverse lower power positive radius
  have cancel := highPowerSlopeCurve_cancel lower power positive radius
  have omegaNonzero := (annularOmegaCurve_pos lower length positive mode radius).ne'
  change ((highPowerSlopeCurve lower (-power) positive radius /
        annularOmegaCurve lower length positive mode radius) *
      highPowerCurve lower power positive radius) • value radius +
    ((highPowerCurve lower (-power) positive radius *
          highPowerCurve lower power positive radius) • slope radius +
      (highPowerCurve lower (-power) positive radius *
        (highPowerSlopeCurve lower power positive radius /
          annularOmegaCurve lower length positive mode radius)) • value radius) = slope radius
  have normalizedCancel :
      highPowerSlopeCurve lower (-power) positive radius /
          annularOmegaCurve lower length positive mode radius *
          highPowerCurve lower power positive radius +
      highPowerCurve lower (-power) positive radius *
          (highPowerSlopeCurve lower power positive radius /
            annularOmegaCurve lower length positive mode radius) = 0 := by
    field_simp [omegaNonzero]
    simpa using cancel
  calc
    _ = ((highPowerSlopeCurve lower (-power) positive radius /
            annularOmegaCurve lower length positive mode radius) *
            highPowerCurve lower power positive radius +
          highPowerCurve lower (-power) positive radius *
            (highPowerSlopeCurve lower power positive radius /
              annularOmegaCurve lower length positive mode radius)) • value radius +
        (highPowerCurve lower (-power) positive radius *
          highPowerCurve lower power positive radius) • slope radius := by module
    _ = slope radius := by rw [normalizedCancel, inverse, zero_smul, one_smul, zero_add]

theorem highBulk_weight_unweight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : AnnularBulk lower) :
    highBulkWeight lower positive bounded (highBulkUnweight lower positive bounded field) = field := by
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded) (field mode)) = field mode
  rw [scalarRadialMap_eq_collarScalar, scalarRadialMap_eq_collarScalar]
  exact collarPower_inverse_apply lower highTiltExponent positive (field mode)

theorem highBulk_unweight_weight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : AnnularBulk lower) :
    highBulkUnweight lower positive bounded (highBulkWeight lower positive bounded field) = field := by
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded)
      (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (field mode)) = field mode
  rw [scalarRadialMap_eq_collarScalar, scalarRadialMap_eq_collarScalar]
  simpa only [neg_neg] using collarPower_inverse_apply lower (-highTiltExponent) positive (field mode)

private theorem highOmega_weight_unweight_slope (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaWeightCoordinates lower length positive bounded
      (highOmegaUnweightCoordinates lower length positive bounded field) 1 = field 1 := by
  rw [highOmegaWeightCoordinates_slope, highOmegaUnweightCoordinates_value,
    highOmegaUnweightCoordinates_slope, map_add]
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
          (highPositivePower_bound lower positive bounded) (field 1 mode)) +
    scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (scalarRadialMap lower (highOmegaSlopeRatio lower length highTiltExponent positive mode)
        (highTiltExponent / 3) (highOmegaPositiveSlope_bound lower length positive bounded mode)
        (field 0 mode)) +
    scalarRadialMap lower (highOmegaSlopeRatio lower length (-highTiltExponent) positive mode)
      (highTiltExponent / 3 * lower ^ (-highTiltExponent))
      (highOmegaNegativeSlope_bound lower length positive bounded mode)
      (scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded) (field 0 mode)) = field 1 mode
  repeat' rw [scalarRadialMap_eq_collarScalar]
  have inverseSlope := collarOmegaPower_inverse_slope lower length highTiltExponent positive mode
    (field 0 mode) (field 1 mode)
  simpa only [map_add, add_comm, add_left_comm, add_assoc] using inverseSlope

theorem highOmegaCoordinates_weight_unweight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaWeightCoordinates lower length positive bounded
      (highOmegaUnweightCoordinates lower length positive bounded field) = field := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change highOmegaWeightCoordinates lower length positive bounded
      (highOmegaUnweightCoordinates lower length positive bounded field) 0 = field 0
    rw [highOmegaWeightCoordinates_value, highOmegaUnweightCoordinates_value,
      highBulk_weight_unweight]
  · exact highOmega_weight_unweight_slope lower length positive bounded field

private theorem highOmega_unweight_weight_slope (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaUnweightCoordinates lower length positive bounded
      (highOmegaWeightCoordinates lower length positive bounded field) 1 = field 1 := by
  rw [highOmegaUnweightCoordinates_slope, highOmegaWeightCoordinates_value,
    highOmegaWeightCoordinates_slope, map_add]
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded)
      (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
          (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (field 1 mode)) +
    scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded)
      (scalarRadialMap lower (highOmegaSlopeRatio lower length (-highTiltExponent) positive mode)
        (highTiltExponent / 3 * lower ^ (-highTiltExponent))
        (highOmegaNegativeSlope_bound lower length positive bounded mode) (field 0 mode)) +
    scalarRadialMap lower (highOmegaSlopeRatio lower length highTiltExponent positive mode)
      (highTiltExponent / 3) (highOmegaPositiveSlope_bound lower length positive bounded mode)
      (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (field 0 mode)) = field 1 mode
  repeat' rw [scalarRadialMap_eq_collarScalar]
  have inverseSlope := collarOmegaPower_inverse_slope lower length (-highTiltExponent) positive mode
    (field 0 mode) (field 1 mode)
  simpa only [neg_neg, map_add, add_comm, add_left_comm, add_assoc] using inverseSlope

theorem highOmegaCoordinates_unweight_weight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaUnweightCoordinates lower length positive bounded
      (highOmegaWeightCoordinates lower length positive bounded field) = field := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change highOmegaUnweightCoordinates lower length positive bounded
      (highOmegaWeightCoordinates lower length positive bounded field) 0 = field 0
    rw [highOmegaUnweightCoordinates_value, highOmegaWeightCoordinates_value,
      highBulk_unweight_weight]
  · exact highOmega_unweight_weight_slope lower length positive bounded field

def highOmegaUnweight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  ((highOmegaUnweightCoordinates lower length positive bounded).comp
    (annularOmegaGraph lower length positive lengthPositive).subtypeL).codRestrict _
      (fun field => highOmegaUnweight_mem lower length positive bounded lengthPositive field.val field.property)

def highOmegaWeight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  ((highOmegaWeightCoordinates lower length positive bounded).comp
    (annularOmegaGraph lower length positive lengthPositive).subtypeL).codRestrict _
      (fun field => highOmegaWeight_mem lower length positive bounded lengthPositive field.val field.property)

def highOmegaTiltEquivalence (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) :
    annularOmegaGraph lower length positive lengthPositive ≃L[ℂ]
      annularOmegaGraph lower length positive lengthPositive where
  toLinearEquiv :=
    { toLinearMap := (highOmegaWeight lower length positive bounded lengthPositive).toLinearMap
      invFun := highOmegaUnweight lower length positive bounded lengthPositive
      left_inv := fun field => Subtype.ext
        (highOmegaCoordinates_unweight_weight lower length positive bounded field.val)
      right_inv := fun field => Subtype.ext
        (highOmegaCoordinates_weight_unweight lower length positive bounded field.val) }
  continuous_toFun := (highOmegaWeight lower length positive bounded lengthPositive).continuous
  continuous_invFun := (highOmegaUnweight lower length positive bounded lengthPositive).continuous

end Grad.AnnularHighTilt
