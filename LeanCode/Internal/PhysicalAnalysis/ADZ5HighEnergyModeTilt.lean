import ADZ4HighOmegaEquivalence
import AAR3FaithfulEnergyRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.ActualReferenceAssembly
open Grad.CircularHighWeak

/-- `V^(-1/2) (r^power)'`, the exact cross coefficient in AAG's stored derivative. -/
def highEnergySlopeRatio (lower length power : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => highPowerSlopeCurve lower power positive radius /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    (highPowerSlopeCurve lower power positive).continuous.div
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

private theorem potentialWeight_radial_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    3 / radius ≤ annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius := by
  have radiusPositive := positive.trans_le inside.1
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have modeBound : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have potentialBound : (mode.val.1 : ℝ) ^ 2 / radius ^ 2 ≤
      annularPotential length radius mode.val.1 mode.val.2 := by
    unfold annularPotential
    exact le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (highMultiplier_nonnegative _) (sq_nonneg _)) (sq_nonneg _))
  have multiplied := (div_le_iff₀ (sq_pos_of_pos radiusPositive)).1 potentialBound
  have productPositive := mul_pos radiusPositive rootPositive
  have productSq : 9 ≤
      (radius * annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) ^ 2 := by
    rw [mul_pow, rootSq]
    nlinarith [sq_abs (mode.val.1 : ℝ)]
  have productBound : 3 ≤ radius *
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius := by nlinarith
  exact (div_le_iff₀ radiusPositive).2 (by simpa [mul_comm] using productBound)

theorem highEnergyPositiveSlope_bound (lower length : ℝ) (positive : 0 < lower)
    (_bounded : lower ≤ 1) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highEnergySlopeRatio lower length highTiltExponent positive mode radius| ≤ highTiltExponent / 3 := by
  have radiusPositive := positive.trans_le inside.1
  have weightPositive := annularPotentialWeight_pos lower length positive mode radius
  have weightBound := potentialWeight_radial_bound lower length positive mode radius inside
  have powerBound : radius ^ highTiltExponent ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow radiusPositive.le inside.2 highTiltExponent_pos.le
  change |highPowerSlopeCurve lower highTiltExponent positive radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ _
  rw [highPowerSlopeCurve_physical lower highTiltExponent positive radius inside,
    abs_div, abs_of_pos weightPositive, abs_mul, abs_of_pos highTiltExponent_pos,
    abs_of_pos (Real.rpow_pos_of_pos radiusPositive _)]
  apply (div_le_iff₀ weightPositive).2
  rw [Real.rpow_sub_one radiusPositive.ne']
  calc
    highTiltExponent * (radius ^ highTiltExponent / radius) ≤
        highTiltExponent * (1 / radius) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right powerBound radiusPositive.le)
        highTiltExponent_pos.le
    _ = (highTiltExponent / 3) * (3 / radius) := by ring
    _ ≤ (highTiltExponent / 3) *
        annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius :=
      mul_le_mul_of_nonneg_left weightBound (by norm_num [highTiltExponent])

theorem highEnergyNegativeSlope_bound (lower length : ℝ) (positive : 0 < lower)
    (_bounded : lower ≤ 1) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highEnergySlopeRatio lower length (-highTiltExponent) positive mode radius| ≤
      highTiltExponent / 3 * lower ^ (-highTiltExponent) := by
  have radiusPositive := positive.trans_le inside.1
  have weightPositive := annularPotentialWeight_pos lower length positive mode radius
  have weightBound := potentialWeight_radial_bound lower length positive mode radius inside
  have powerBound : radius ^ (-highTiltExponent) ≤ lower ^ (-highTiltExponent) :=
    Real.rpow_le_rpow_of_nonpos positive inside.1 (neg_nonpos.mpr highTiltExponent_pos.le)
  change |highPowerSlopeCurve lower (-highTiltExponent) positive radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ _
  rw [highPowerSlopeCurve_physical lower (-highTiltExponent) positive radius inside,
    abs_div, abs_of_pos weightPositive, abs_mul, abs_neg, abs_of_pos highTiltExponent_pos,
    abs_of_pos (Real.rpow_pos_of_pos radiusPositive _)]
  apply (div_le_iff₀ weightPositive).2
  rw [Real.rpow_sub_one radiusPositive.ne']
  calc
    highTiltExponent * (radius ^ (-highTiltExponent) / radius) ≤
        highTiltExponent * (lower ^ (-highTiltExponent) / radius) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right powerBound radiusPositive.le)
        highTiltExponent_pos.le
    _ = (highTiltExponent / 3 * lower ^ (-highTiltExponent)) * (3 / radius) := by ring
    _ ≤ (highTiltExponent / 3 * lower ^ (-highTiltExponent)) *
        annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius :=
      mul_le_mul_of_nonneg_left weightBound
        (mul_nonneg (by norm_num [highTiltExponent]) (Real.rpow_pos_of_pos positive _).le)

/-- Multiplication of a genuine complex smooth radial core by the global
smooth representative of `r^power`. -/
def highPowerComplexCore (lower power : ℝ) (positive : 0 < lower) :
    complexSmoothRadialCore 1 →ₗ[ℂ] complexSmoothRadialCore 1 where
  toFun core := acceptedCoreToComplex 1
    (smoothRadialFunctionCore
      ((Complex.ofRealCLM ∘ highPowerCurve lower power positive) • (core.val.1 : ℝ → ComplexEuclidean 1))
      ((Complex.ofRealCLM.contDiff.comp (highPowerCurve_smooth lower power positive)).smul core.property.1))
  map_add' first second := by
    apply complexSmoothRadialCore_ext
    intro radius
    change (highPowerCurve lower power positive radius : ℂ) •
      (first.val.1 radius + second.val.1 radius) =
      (highPowerCurve lower power positive radius : ℂ) • first.val.1 radius +
        (highPowerCurve lower power positive radius : ℂ) • second.val.1 radius
    exact smul_add _ _ _
  map_smul' scalar core := by
    apply complexSmoothRadialCore_ext
    intro radius
    exact smul_comm (highPowerCurve lower power positive radius : ℂ) scalar (core.val.1 radius)

@[simp] theorem highPowerComplexCore_value (lower power : ℝ) (positive : 0 < lower)
    (core : complexSmoothRadialCore 1) (radius : ℝ) :
    (highPowerComplexCore lower power positive core).val.1 radius =
      (highPowerCurve lower power positive radius : ℂ) • core.val.1 radius := rfl

theorem highPowerComplexCore_slope (lower power : ℝ) (positive : 0 < lower)
    (core : complexSmoothRadialCore 1) (radius : ℝ) :
    (highPowerComplexCore lower power positive core).val.2 radius =
      (highPowerCurve lower power positive radius : ℂ) • core.val.2 radius +
        (highPowerSlopeCurve lower power positive radius : ℂ) • core.val.1 radius := by
  have scalarDerivative := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt radius
    (highPowerCurve_hasDerivAt lower power positive radius)
  have derivative := scalarDerivative.smul
    (core.property.2 radius)
  exact (highPowerComplexCore lower power positive core).property.2 radius |>.unique derivative

/-- One-mode AAG coordinate action of `r^(9/4)`. -/
def highModeEnergyUnweight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) : AnnularModeEnergyAmbient lower →L[ℂ] AnnularModeEnergyAmbient lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    (((scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded)).comp (annularModeDerivative lower) +
      (scalarRadialMap lower (highEnergySlopeRatio lower length highTiltExponent positive mode)
        (highTiltExponent / 3) (highEnergyPositiveSlope_bound lower length positive bounded mode)).comp
          (annularModeMass lower)).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
        (((scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
          (highPositivePower_bound lower positive bounded)).comp (annularModeMass lower)).prod
            (annularModeOuter lower))))

/-- One-mode inverse AAG coordinate action of `r^(-9/4)`. -/
def highModeEnergyWeight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) : AnnularModeEnergyAmbient lower →L[ℂ] AnnularModeEnergyAmbient lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    (((scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)).comp
          (annularModeDerivative lower) +
      (scalarRadialMap lower (highEnergySlopeRatio lower length (-highTiltExponent) positive mode)
        (highTiltExponent / 3 * lower ^ (-highTiltExponent))
        (highEnergyNegativeSlope_bound lower length positive bounded mode)).comp
          (annularModeMass lower)).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
        (((scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
          (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)).comp
            (annularModeMass lower)).prod (annularModeOuter lower))))

end Grad.AnnularHighTilt
