import ADZ1SmoothHighPowers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularFluxTrace Grad.AnnularOmegaGraph

/-- The product-rule term `omega^-1 (r^power)'`, mode by mode. -/
def highOmegaSlopeRatio (lower length power : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => highPowerSlopeCurve lower power positive radius /
      annularOmegaCurve lower length positive mode radius,
    (highPowerSlopeCurve lower power positive).continuous.div
      (annularOmegaCurve lower length positive mode).continuous
      (fun radius => (annularOmegaCurve_pos lower length positive mode radius).ne')⟩

theorem highOmegaPositiveSlope_bound (lower length : ℝ) (positive : 0 < lower)
    (_bounded : lower ≤ 1) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highOmegaSlopeRatio lower length highTiltExponent positive mode radius| ≤ highTiltExponent / 3 := by
  have radiusPositive := positive.trans_le inside.1
  have omegaPositive := annularOmegaCurve_pos lower length positive mode radius
  have angular := annularOmega_angular length radius radiusPositive mode
  have modeBound : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have omegaThree : 3 ≤ annularOmegaCurve lower length positive mode radius := by
    have curvePhysical : annularOmegaCurve lower length positive mode radius = annularOmega length radius mode := by
      change annularOmega length (max lower radius) mode = _
      rw [max_eq_right inside.1]
    rw [curvePhysical]
    have divided := div_le_div_of_nonneg_right modeBound radiusPositive.le
    have radiusInverse : 1 ≤ radius⁻¹ := (one_le_inv₀ radiusPositive).mpr inside.2
    rw [div_eq_mul_inv] at divided
    have three : 3 ≤ 3 * radius⁻¹ := by nlinarith
    exact three.trans (divided.trans angular)
  have powerBound : radius ^ (highTiltExponent - 1) ≤ 1 := by
    have exponent : 0 ≤ highTiltExponent - 1 := by norm_num [highTiltExponent]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow radiusPositive.le inside.2 exponent
  change |highPowerSlopeCurve lower highTiltExponent positive radius /
    annularOmegaCurve lower length positive mode radius| ≤ _
  rw [highPowerSlopeCurve_physical lower highTiltExponent positive radius inside,
    abs_div, abs_of_pos omegaPositive, abs_mul,
    abs_of_pos highTiltExponent_pos, abs_of_pos (Real.rpow_pos_of_pos radiusPositive _)]
  apply (div_le_iff₀ omegaPositive).2
  calc
    highTiltExponent * radius ^ (highTiltExponent - 1) ≤ highTiltExponent * 1 :=
      mul_le_mul_of_nonneg_left powerBound highTiltExponent_pos.le
    _ ≤ (highTiltExponent / 3) * annularOmegaCurve lower length positive mode radius := by
      nlinarith [highTiltExponent_pos]

theorem highOmegaNegativeSlope_bound (lower length : ℝ) (positive : 0 < lower)
    (_bounded : lower ≤ 1) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highOmegaSlopeRatio lower length (-highTiltExponent) positive mode radius| ≤
      highTiltExponent / 3 * lower ^ (-highTiltExponent) := by
  have radiusPositive := positive.trans_le inside.1
  have omegaPositive := annularOmegaCurve_pos lower length positive mode radius
  have angular := annularOmega_angular length radius radiusPositive mode
  have modeBound : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have omegaBound : 3 / radius ≤ annularOmegaCurve lower length positive mode radius := by
    have curvePhysical : annularOmegaCurve lower length positive mode radius = annularOmega length radius mode := by
      change annularOmega length (max lower radius) mode = _
      rw [max_eq_right inside.1]
    rw [curvePhysical]
    exact (div_le_div_of_nonneg_right modeBound radiusPositive.le).trans angular
  have powerBound : radius ^ (-highTiltExponent) ≤ lower ^ (-highTiltExponent) :=
    Real.rpow_le_rpow_of_nonpos positive inside.1 (neg_nonpos.mpr highTiltExponent_pos.le)
  change |highPowerSlopeCurve lower (-highTiltExponent) positive radius /
    annularOmegaCurve lower length positive mode radius| ≤ _
  rw [highPowerSlopeCurve_physical lower (-highTiltExponent) positive radius inside,
    abs_div, abs_of_pos omegaPositive, abs_mul, abs_neg,
    abs_of_pos highTiltExponent_pos, abs_of_pos (Real.rpow_pos_of_pos radiusPositive _)]
  apply (div_le_iff₀ omegaPositive).2
  rw [Real.rpow_sub_one radiusPositive.ne']
  calc
    highTiltExponent * (radius ^ (-highTiltExponent) / radius) ≤
        highTiltExponent * (lower ^ (-highTiltExponent) / radius) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right powerBound radiusPositive.le)
        highTiltExponent_pos.le
    _ = (highTiltExponent / 3 * lower ^ (-highTiltExponent)) * (3 / radius) := by ring
    _ ≤ (highTiltExponent / 3 * lower ^ (-highTiltExponent)) *
        annularOmegaCurve lower length positive mode radius :=
      mul_le_mul_of_nonneg_left omegaBound
        (mul_nonneg (by norm_num [highTiltExponent]) (Real.rpow_pos_of_pos positive _).le)

/-- Multiplication by `r^(9/4)` on every high bulk mode. -/
def highBulkUnweight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun _ => highPowerCurve lower highTiltExponent positive) 1
    (by norm_num) (fun _ => highPositivePower_bound lower positive bounded)

/-- Multiplication by `r^(-9/4)` on every high bulk mode. -/
def highBulkWeight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun _ => highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (Real.rpow_pos_of_pos positive _).le
    (fun _ => highNegativePower_bound lower positive bounded)

def highOmegaUnweightSlopeTerm (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (highOmegaSlopeRatio lower length highTiltExponent positive)
    (highTiltExponent / 3) (by norm_num [highTiltExponent])
    (highOmegaPositiveSlope_bound lower length positive bounded)

def highOmegaWeightSlopeTerm (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (highOmegaSlopeRatio lower length (-highTiltExponent) positive)
    (highTiltExponent / 3 * lower ^ (-highTiltExponent))
    (mul_nonneg (by norm_num [highTiltExponent]) (Real.rpow_pos_of_pos positive _).le)
    (highOmegaNegativeSlope_bound lower length positive bounded)

theorem highBulkUnweight_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : AnnularBulk lower) : ‖highBulkUnweight lower positive bounded field‖ ≤ ‖field‖ := by
  simpa only [highBulkUnweight, one_mul] using annularScalarFamily_bound lower
    (fun _ : HighAnnularMode => highPowerCurve lower highTiltExponent positive) 1 (by norm_num)
    (fun _ => highPositivePower_bound lower positive bounded) field

theorem highBulkWeight_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : AnnularBulk lower) :
    ‖highBulkWeight lower positive bounded field‖ ≤ lower ^ (-highTiltExponent) * ‖field‖ :=
  annularScalarFamily_bound lower
    (fun _ : HighAnnularMode => highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (Real.rpow_pos_of_pos positive _).le
    (fun _ => highNegativePower_bound lower positive bounded) field

theorem highOmegaUnweightSlopeTerm_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularBulk lower) :
    ‖highOmegaUnweightSlopeTerm lower length positive bounded field‖ ≤
      (highTiltExponent / 3) * ‖field‖ :=
  annularScalarFamily_bound lower (highOmegaSlopeRatio lower length highTiltExponent positive)
    (highTiltExponent / 3) (by norm_num [highTiltExponent])
    (highOmegaPositiveSlope_bound lower length positive bounded) field

theorem highOmegaWeightSlopeTerm_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : AnnularBulk lower) :
    ‖highOmegaWeightSlopeTerm lower length positive bounded field‖ ≤
      (highTiltExponent / 3 * lower ^ (-highTiltExponent)) * ‖field‖ :=
  annularScalarFamily_bound lower (highOmegaSlopeRatio lower length (-highTiltExponent) positive)
    (highTiltExponent / 3 * lower ^ (-highTiltExponent))
    (mul_nonneg (by norm_num [highTiltExponent]) (Real.rpow_pos_of_pos positive _).le)
    (highOmegaNegativeSlope_bound lower length positive bounded) field

end Grad.AnnularHighTilt
