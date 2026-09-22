import ADZ7HighEnergyCompletedTilt

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem scalarRadialPower_inverse (lower power : ℝ) (positive : 0 < lower)
    (firstBound secondBound : ℝ)
    (firstLaw : ∀ radius ∈ Icc lower 1,
      |highPowerCurve lower (-power) positive radius| ≤ firstBound)
    (secondLaw : ∀ radius ∈ Icc lower 1,
      |highPowerCurve lower power positive radius| ≤ secondBound)
    (field : RadialL2 1 lower) :
    scalarRadialMap lower (highPowerCurve lower (-power) positive) firstBound firstLaw
      (scalarRadialMap lower (highPowerCurve lower power positive) secondBound secondLaw field) = field := by
  rw [scalarRadialMap_eq_collarScalar, scalarRadialMap_eq_collarScalar,
    collarScalar_mul_apply]
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower
    (highPowerCurve lower (-power) positive * highPowerCurve lower power positive) field]
    with radius equality
  rw [equality]
  change (highPowerCurve lower (-power) positive radius *
    highPowerCurve lower power positive radius) • field radius = field radius
  rw [highPowerCurve_inverse, one_smul]

private theorem highEnergyPower_inverse_derivative (lower length power : ℝ)
    (positive : 0 < lower) (mode : HighAnnularMode)
    (negativePowerBound positivePowerBound negativeSlopeBound positiveSlopeBound : ℝ)
    (negativePowerLaw : ∀ radius ∈ Icc lower 1,
      |highPowerCurve lower (-power) positive radius| ≤ negativePowerBound)
    (positivePowerLaw : ∀ radius ∈ Icc lower 1,
      |highPowerCurve lower power positive radius| ≤ positivePowerBound)
    (negativeSlopeLaw : ∀ radius ∈ Icc lower 1,
      |highEnergySlopeRatio lower length (-power) positive mode radius| ≤ negativeSlopeBound)
    (positiveSlopeLaw : ∀ radius ∈ Icc lower 1,
      |highEnergySlopeRatio lower length power positive mode radius| ≤ positiveSlopeBound)
    (value slope : RadialL2 1 lower) :
    scalarRadialMap lower (highPowerCurve lower (-power) positive) negativePowerBound negativePowerLaw
        (scalarRadialMap lower (highPowerCurve lower power positive) positivePowerBound positivePowerLaw slope +
          scalarRadialMap lower (highEnergySlopeRatio lower length power positive mode)
            positiveSlopeBound positiveSlopeLaw value) +
      scalarRadialMap lower (highEnergySlopeRatio lower length (-power) positive mode)
        negativeSlopeBound negativeSlopeLaw
        (scalarRadialMap lower (highPowerCurve lower power positive) positivePowerBound positivePowerLaw value) =
      slope := by
  repeat' rw [scalarRadialMap_eq_collarScalar]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (collarScalar 1 lower (highPowerCurve lower (-power) positive)
        (collarScalar 1 lower (highPowerCurve lower power positive) slope +
          collarScalar 1 lower (highEnergySlopeRatio lower length power positive mode) value))
      (collarScalar 1 lower (highEnergySlopeRatio lower length (-power) positive mode)
        (collarScalar 1 lower (highPowerCurve lower power positive) value)),
    collarScalar_ae 1 lower (highPowerCurve lower (-power) positive)
      (collarScalar 1 lower (highPowerCurve lower power positive) slope +
        collarScalar 1 lower (highEnergySlopeRatio lower length power positive mode) value),
    Lp.coeFn_add (collarScalar 1 lower (highPowerCurve lower power positive) slope)
      (collarScalar 1 lower (highEnergySlopeRatio lower length power positive mode) value),
    collarScalar_ae 1 lower (highPowerCurve lower power positive) slope,
    collarScalar_ae 1 lower (highEnergySlopeRatio lower length power positive mode) value,
    collarScalar_ae 1 lower (highEnergySlopeRatio lower length (-power) positive mode)
      (collarScalar 1 lower (highPowerCurve lower power positive) value),
    collarScalar_ae 1 lower (highPowerCurve lower power positive) value]
    with radius total negativeProduct inner positiveSlope positiveRatio negativeRatio positiveValue
  rw [total, Pi.add_apply, negativeProduct, inner, Pi.add_apply, positiveSlope,
    positiveRatio, negativeRatio, positiveValue, smul_add, smul_smul, smul_smul, smul_smul]
  have inverse := highPowerCurve_inverse lower power positive radius
  have cancel := highPowerSlopeCurve_cancel lower power positive radius
  have potentialNonzero := (annularPotentialWeight_pos lower length positive mode radius).ne'
  change ((highPowerCurve lower (-power) positive radius *
          highPowerCurve lower power positive radius) • slope radius +
      (highPowerCurve lower (-power) positive radius *
        (highPowerSlopeCurve lower power positive radius /
          annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)) • value radius) +
    ((highPowerSlopeCurve lower (-power) positive radius /
        annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) *
      highPowerCurve lower power positive radius) • value radius = slope radius
  have normalizedCancel :
      highPowerCurve lower (-power) positive radius *
          (highPowerSlopeCurve lower power positive radius /
            annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) +
        (highPowerSlopeCurve lower (-power) positive radius /
            annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) *
          highPowerCurve lower power positive radius = 0 := by
    field_simp [potentialNonzero]
    simpa [add_comm] using cancel
  calc
    _ = (highPowerCurve lower (-power) positive radius *
          highPowerCurve lower power positive radius) • slope radius +
        (highPowerCurve lower (-power) positive radius *
            (highPowerSlopeCurve lower power positive radius /
              annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) +
          (highPowerSlopeCurve lower (-power) positive radius /
              annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) *
            highPowerCurve lower power positive radius) • value radius := by module
    _ = slope radius := by rw [inverse, normalizedCancel, one_smul, zero_smul, add_zero]

private theorem highModeEnergy_weight_unweight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    highModeEnergyWeight lower length positive bounded mode
      (highModeEnergyUnweight lower length positive bounded mode field) = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · change annularModeDerivative lower (highModeEnergyWeight lower length positive bounded mode
      (highModeEnergyUnweight lower length positive bounded mode field)) = annularModeDerivative lower field
    rw [highModeEnergyWeight_derivative, highModeEnergyUnweight_derivative,
      highModeEnergyUnweight_mass]
    exact highEnergyPower_inverse_derivative lower length highTiltExponent positive mode
      (lower ^ (-highTiltExponent)) 1
      (highTiltExponent / 3 * lower ^ (-highTiltExponent)) (highTiltExponent / 3)
      (highNegativePower_bound lower positive bounded) (highPositivePower_bound lower positive bounded)
      (highEnergyNegativeSlope_bound lower length positive bounded mode)
      (highEnergyPositiveSlope_bound lower length positive bounded mode)
      (annularModeMass lower field) (annularModeDerivative lower field)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    apply Prod.ext
    · change annularModeMass lower (highModeEnergyWeight lower length positive bounded mode
        (highModeEnergyUnweight lower length positive bounded mode field)) = annularModeMass lower field
      rw [highModeEnergyWeight_mass, highModeEnergyUnweight_mass]
      exact scalarRadialPower_inverse lower highTiltExponent positive
        (lower ^ (-highTiltExponent)) 1
        (highNegativePower_bound lower positive bounded) (highPositivePower_bound lower positive bounded)
        (annularModeMass lower field)
    · change annularModeOuter lower (highModeEnergyWeight lower length positive bounded mode
        (highModeEnergyUnweight lower length positive bounded mode field)) = annularModeOuter lower field
      rw [highModeEnergyWeight_outer, highModeEnergyUnweight_outer]

private theorem highModeEnergy_unweight_weight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    highModeEnergyUnweight lower length positive bounded mode
      (highModeEnergyWeight lower length positive bounded mode field) = field := by
  have positiveLaw : ∀ radius ∈ Icc lower 1,
      |highPowerCurve lower (-(-highTiltExponent)) positive radius| ≤ 1 := by
    intro radius inside
    simpa only [neg_neg] using highPositivePower_bound lower positive bounded radius inside
  have positiveSlopeLaw : ∀ radius ∈ Icc lower 1,
      |highEnergySlopeRatio lower length (-(-highTiltExponent)) positive mode radius| ≤
        highTiltExponent / 3 := by
    intro radius inside
    simpa only [neg_neg] using
      highEnergyPositiveSlope_bound lower length positive bounded mode radius inside
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · change annularModeDerivative lower (highModeEnergyUnweight lower length positive bounded mode
      (highModeEnergyWeight lower length positive bounded mode field)) = annularModeDerivative lower field
    rw [highModeEnergyUnweight_derivative, highModeEnergyWeight_derivative,
      highModeEnergyWeight_mass]
    simpa only [neg_neg] using highEnergyPower_inverse_derivative lower length (-highTiltExponent) positive mode
      1 (lower ^ (-highTiltExponent)) (highTiltExponent / 3)
      (highTiltExponent / 3 * lower ^ (-highTiltExponent))
      positiveLaw
      (highNegativePower_bound lower positive bounded)
      positiveSlopeLaw
      (highEnergyNegativeSlope_bound lower length positive bounded mode)
      (annularModeMass lower field) (annularModeDerivative lower field)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    apply Prod.ext
    · change annularModeMass lower (highModeEnergyUnweight lower length positive bounded mode
        (highModeEnergyWeight lower length positive bounded mode field)) = annularModeMass lower field
      rw [highModeEnergyUnweight_mass, highModeEnergyWeight_mass]
      simpa only [neg_neg] using scalarRadialPower_inverse lower (-highTiltExponent) positive
        1 (lower ^ (-highTiltExponent))
        positiveLaw
        (highNegativePower_bound lower positive bounded)
        (annularModeMass lower field)
    · change annularModeOuter lower (highModeEnergyUnweight lower length positive bounded mode
        (highModeEnergyWeight lower length positive bounded mode field)) = annularModeOuter lower field
      rw [highModeEnergyUnweight_outer, highModeEnergyWeight_outer]

theorem highEnergyAmbient_weight_unweight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularEnergyAmbient lower) :
    highEnergyWeightAmbient lower length positive bounded
      (highEnergyUnweightAmbient lower length positive bounded field) = field := by
  apply lp.ext
  funext mode
  change highModeEnergyWeight lower length positive bounded mode
    (highModeEnergyUnweight lower length positive bounded mode (field mode)) = field mode
  exact highModeEnergy_weight_unweight lower length positive bounded mode (field mode)

theorem highEnergyAmbient_unweight_weight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularEnergyAmbient lower) :
    highEnergyUnweightAmbient lower length positive bounded
      (highEnergyWeightAmbient lower length positive bounded field) = field := by
  apply lp.ext
  funext mode
  change highModeEnergyUnweight lower length positive bounded mode
    (highModeEnergyWeight lower length positive bounded mode (field mode)) = field mode
  exact highModeEnergy_unweight_weight lower length positive bounded mode (field mode)

theorem highEnergy_weight_unweight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive) :
    highEnergyWeight lower length positive bounded
      (highEnergyUnweight lower length positive bounded field) = field := by
  apply Subtype.ext
  exact highEnergyAmbient_weight_unweight lower length positive bounded field.val

theorem highEnergy_unweight_weight (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive) :
    highEnergyUnweight lower length positive bounded
      (highEnergyWeight lower length positive bounded field) = field := by
  apply Subtype.ext
  exact highEnergyAmbient_unweight_weight lower length positive bounded field.val

/-- Exact completed AAG high-energy equivalence.  The forward map is the BF
weight `r^(-9/4)` and its inverse is multiplication by `r^(9/4)`. -/
def highEnergyTiltEquivalence (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    annularEnergySpace lower length positive ≃L[ℂ] annularEnergySpace lower length positive where
  toLinearEquiv :=
    { toLinearMap := (highEnergyWeight lower length positive bounded).toLinearMap
      invFun := highEnergyUnweight lower length positive bounded
      left_inv := highEnergy_unweight_weight lower length positive bounded
      right_inv := highEnergy_weight_unweight lower length positive bounded }
  continuous_toFun := (highEnergyWeight lower length positive bounded).continuous
  continuous_invFun := (highEnergyUnweight lower length positive bounded).continuous

theorem highEnergyUnweight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive) :
    ‖highEnergyUnweight lower length positive bounded field‖ ≤ 3 * ‖field‖ := by
  change ‖highEnergyUnweightAmbient lower length positive bounded field.val‖ ≤ 3 * ‖field.val‖
  exact complexLpTwoMap_bound (highModeEnergyUnweight lower length positive bounded) 3
    (by norm_num) (highModeEnergyUnweight_bound lower length positive bounded) field.val

theorem highEnergyWeight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive) :
    ‖highEnergyWeight lower length positive bounded field‖ ≤
      (3 * lower ^ (-highTiltExponent)) * ‖field‖ := by
  change ‖highEnergyWeightAmbient lower length positive bounded field.val‖ ≤
    (3 * lower ^ (-highTiltExponent)) * ‖field.val‖
  exact complexLpTwoMap_bound (highModeEnergyWeight lower length positive bounded)
    (3 * lower ^ (-highTiltExponent))
    (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos positive _).le)
    (highModeEnergyWeight_bound lower length positive bounded) field.val

end Grad.AnnularHighTilt
