import ADZ2HighOmegaMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The literal product-rule action of `r^(9/4)` on BOTH Domega coordinates. -/
def highOmegaUnweightCoordinates (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularOmegaAmbient lower →L[ℂ] AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (highBulkUnweight lower positive bounded).comp (annularOmegaValue lower),
      (highBulkUnweight lower positive bounded).comp (annularOmegaSlope lower) +
        (highOmegaUnweightSlopeTerm lower length positive bounded).comp (annularOmegaValue lower)])

/-- The literal inverse product-rule action of `r^(-9/4)`. -/
def highOmegaWeightCoordinates (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularOmegaAmbient lower →L[ℂ] AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (highBulkWeight lower positive bounded).comp (annularOmegaValue lower),
      (highBulkWeight lower positive bounded).comp (annularOmegaSlope lower) +
        (highOmegaWeightSlopeTerm lower length positive bounded).comp (annularOmegaValue lower)])

@[simp] theorem highOmegaUnweightCoordinates_value (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaUnweightCoordinates lower length positive bounded field 0 =
      highBulkUnweight lower positive bounded (field 0) := rfl

@[simp] theorem highOmegaUnweightCoordinates_slope (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaUnweightCoordinates lower length positive bounded field 1 =
      highBulkUnweight lower positive bounded (field 1) +
        highOmegaUnweightSlopeTerm lower length positive bounded (field 0) := rfl

@[simp] theorem highOmegaWeightCoordinates_value (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaWeightCoordinates lower length positive bounded field 0 =
      highBulkWeight lower positive bounded (field 0) := rfl

@[simp] theorem highOmegaWeightCoordinates_slope (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularOmegaAmbient lower) :
    highOmegaWeightCoordinates lower length positive bounded field 1 =
      highBulkWeight lower positive bounded (field 1) +
        highOmegaWeightSlopeTerm lower length positive bounded (field 0) := rfl

private theorem omegaProductSlopeIdentity (lower length power : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (value slope : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularOmegaCurve lower length positive mode)
        (collarScalar 1 lower (highPowerCurve lower power positive) slope +
          collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value) =
      collarScalar 1 lower (highPowerSlopeCurve lower power positive) value +
        collarScalar 1 lower (highPowerCurve lower power positive)
          (collarScalar 1 lower (annularOmegaCurve lower length positive mode) slope) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (collarScalar 1 lower (highPowerCurve lower power positive) slope)
      (collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value),
    collarScalar_ae 1 lower (annularOmegaCurve lower length positive mode)
      (collarScalar 1 lower (highPowerCurve lower power positive) slope +
        collarScalar 1 lower (highOmegaSlopeRatio lower length power positive mode) value),
    collarScalar_ae 1 lower (highPowerCurve lower power positive) slope,
    collarScalar_ae 1 lower (highOmegaSlopeRatio lower length power positive mode) value,
    Lp.coeFn_add (collarScalar 1 lower (highPowerSlopeCurve lower power positive) value)
      (collarScalar 1 lower (highPowerCurve lower power positive)
        (collarScalar 1 lower (annularOmegaCurve lower length positive mode) slope)),
    collarScalar_ae 1 lower (highPowerSlopeCurve lower power positive) value,
    collarScalar_ae 1 lower (highPowerCurve lower power positive)
      (collarScalar 1 lower (annularOmegaCurve lower length positive mode) slope),
    collarScalar_ae 1 lower (annularOmegaCurve lower length positive mode) slope]
    with radius inputSum outer powerValue ratioValue outputSum derivativeValue powerSlope omegaSlope
  rw [outer, inputSum, Pi.add_apply, powerValue, ratioValue, outputSum, Pi.add_apply,
    derivativeValue, powerSlope, omegaSlope]
  change annularOmegaCurve lower length positive mode radius •
      (highPowerCurve lower power positive radius • slope radius +
        (highPowerSlopeCurve lower power positive radius /
          annularOmegaCurve lower length positive mode radius) • value radius) =
    highPowerSlopeCurve lower power positive radius • value radius +
      highPowerCurve lower power positive radius •
        (annularOmegaCurve lower length positive mode radius • slope radius)
  rw [smul_add, smul_smul, smul_smul, smul_smul]
  have ratio : annularOmegaCurve lower length positive mode radius *
      (highPowerSlopeCurve lower power positive radius /
        annularOmegaCurve lower length positive mode radius) =
      highPowerSlopeCurve lower power positive radius := by
    field_simp [(annularOmegaCurve_pos lower length positive mode radius).ne']
  rw [ratio, mul_comm (annularOmegaCurve lower length positive mode radius)
    (highPowerCurve lower power positive radius)]
  exact add_comm _ _

theorem highOmegaUnweight_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) (field : AnnularOmegaAmbient lower)
    (member : field ∈ annularOmegaGraph lower length positive lengthPositive) :
    highOmegaUnweightCoordinates lower length positive bounded field ∈
      annularOmegaGraph lower length positive lengthPositive := by
  rw [annularOmegaGraph_mem_iff lower length positive lengthPositive] at member ⊢
  intro mode
  have valueOrd : radialOrdinary 1 lower positive
      (highOmegaUnweightCoordinates lower length positive bounded field 0 mode) =
      collarScalar 1 lower (highPowerCurve lower highTiltExponent positive)
        (radialOrdinary 1 lower positive (field 0 mode)) := by
    rw [highOmegaUnweightCoordinates_value]
    exact annularScalarFamily_ordinary lower positive _ 1 (by norm_num)
      (fun _ => highPositivePower_bound lower positive bounded) _ mode
  have slopeOrd : radialOrdinary 1 lower positive
      (highOmegaUnweightCoordinates lower length positive bounded field 1 mode) =
      collarScalar 1 lower (highPowerCurve lower highTiltExponent positive)
          (radialOrdinary 1 lower positive (field 1 mode)) +
        collarScalar 1 lower (highOmegaSlopeRatio lower length highTiltExponent positive mode)
          (radialOrdinary 1 lower positive (field 0 mode)) := by
    rw [highOmegaUnweightCoordinates_slope]
    change radialOrdinary 1 lower positive
      ((highBulkUnweight lower positive bounded (field 1)) mode +
        (highOmegaUnweightSlopeTerm lower length positive bounded (field 0)) mode) = _
    rw [map_add]
    congr 1
    · exact annularScalarFamily_ordinary lower positive _ 1 (by norm_num)
        (fun _ => highPositivePower_bound lower positive bounded) _ mode
    · exact annularScalarFamily_ordinary lower positive _ (highTiltExponent / 3)
        (by norm_num [highTiltExponent])
        (highOmegaPositiveSlope_bound lower length positive bounded) _ mode
  rw [valueOrd, slopeOrd, omegaProductSlopeIdentity lower length highTiltExponent positive mode]
  exact collarWeakDerivative_scalar lower (highPowerCurve lower highTiltExponent positive)
    (highPowerSlopeCurve lower highTiltExponent positive)
    (highPowerCurve_hasDerivAt lower highTiltExponent positive) _ _ (member mode)

theorem highOmegaWeight_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) (field : AnnularOmegaAmbient lower)
    (member : field ∈ annularOmegaGraph lower length positive lengthPositive) :
    highOmegaWeightCoordinates lower length positive bounded field ∈
      annularOmegaGraph lower length positive lengthPositive := by
  rw [annularOmegaGraph_mem_iff lower length positive lengthPositive] at member ⊢
  intro mode
  have valueOrd : radialOrdinary 1 lower positive
      (highOmegaWeightCoordinates lower length positive bounded field 0 mode) =
      collarScalar 1 lower (highPowerCurve lower (-highTiltExponent) positive)
        (radialOrdinary 1 lower positive (field 0 mode)) := by
    rw [highOmegaWeightCoordinates_value]
    exact annularScalarFamily_ordinary lower positive _ (lower ^ (-highTiltExponent))
      (Real.rpow_pos_of_pos positive _).le
      (fun _ => highNegativePower_bound lower positive bounded) _ mode
  have slopeOrd : radialOrdinary 1 lower positive
      (highOmegaWeightCoordinates lower length positive bounded field 1 mode) =
      collarScalar 1 lower (highPowerCurve lower (-highTiltExponent) positive)
          (radialOrdinary 1 lower positive (field 1 mode)) +
        collarScalar 1 lower (highOmegaSlopeRatio lower length (-highTiltExponent) positive mode)
          (radialOrdinary 1 lower positive (field 0 mode)) := by
    rw [highOmegaWeightCoordinates_slope]
    change radialOrdinary 1 lower positive
      ((highBulkWeight lower positive bounded (field 1)) mode +
        (highOmegaWeightSlopeTerm lower length positive bounded (field 0)) mode) = _
    rw [map_add]
    congr 1
    · exact annularScalarFamily_ordinary lower positive _ (lower ^ (-highTiltExponent))
        (Real.rpow_pos_of_pos positive _).le
        (fun _ => highNegativePower_bound lower positive bounded) _ mode
    · exact annularScalarFamily_ordinary lower positive _
        (highTiltExponent / 3 * lower ^ (-highTiltExponent))
        (mul_nonneg (by norm_num [highTiltExponent]) (Real.rpow_pos_of_pos positive _).le)
        (highOmegaNegativeSlope_bound lower length positive bounded) _ mode
  rw [valueOrd, slopeOrd, omegaProductSlopeIdentity lower length (-highTiltExponent) positive mode]
  exact collarWeakDerivative_scalar lower (highPowerCurve lower (-highTiltExponent) positive)
    (highPowerSlopeCurve lower (-highTiltExponent) positive)
    (highPowerCurve_hasDerivAt lower (-highTiltExponent) positive) _ _ (member mode)

end Grad.AnnularHighTilt
