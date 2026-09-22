import ADZ6HighEnergyCoreAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction

theorem highModeEnergyUnweight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    ‖highModeEnergyUnweight lower length positive bounded mode field‖ ≤ 3 * ‖field‖ := by
  have inputSq := annularModeEnergy_norm_sq lower field
  have outputSq := annularModeEnergy_norm_sq lower
    (highModeEnergyUnweight lower length positive bounded mode field)
  have derivative := highModeEnergyUnweight_derivative lower length positive bounded mode field
  have derivativeBound : ‖annularModeDerivative lower
      (highModeEnergyUnweight lower length positive bounded mode field)‖ ≤
      ‖annularModeDerivative lower field‖ + (highTiltExponent / 3) * ‖annularModeMass lower field‖ := by
    rw [derivative]
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [one_mul] using (scalarRadialMap_bound lower
        (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded) (annularModeDerivative lower field)))
      (scalarRadialMap_bound lower (highEnergySlopeRatio lower length highTiltExponent positive mode)
        (highTiltExponent / 3) (highEnergyPositiveSlope_bound lower length positive bounded mode)
        (annularModeMass lower field)))
  have massBound : ‖annularModeMass lower
      (highModeEnergyUnweight lower length positive bounded mode field)‖ ≤ ‖annularModeMass lower field‖ := by
    rw [highModeEnergyUnweight_mass]
    simpa only [one_mul] using scalarRadialMap_bound lower
      (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded) (annularModeMass lower field)
  have outerEq := highModeEnergyUnweight_outer lower length positive bounded mode field
  have derivativeInput := annularModeDerivative_bound lower field
  have massInput := annularModeMass_bound lower field
  have outerInput := annularModeOuter_bound lower field
  have exponentRatio : highTiltExponent / 3 = 3 / 4 := by norm_num [highTiltExponent]
  rw [exponentRatio] at derivativeBound
  rw [outerEq] at outputSq
  have derivativeBound' : ‖annularModeDerivative lower
      (highModeEnergyUnweight lower length positive bounded mode field)‖ ≤ 2 * ‖field‖ := by
    calc
      _ ≤ ‖annularModeDerivative lower field‖ + (3 / 4) * ‖annularModeMass lower field‖ :=
        derivativeBound
      _ ≤ ‖field‖ + (3 / 4) * ‖field‖ := by
        gcongr
        · simpa only [one_mul] using derivativeInput
        · simpa only [one_mul] using massInput
      _ ≤ 2 * ‖field‖ := by nlinarith [norm_nonneg field]
  have massBound' : ‖annularModeMass lower
      (highModeEnergyUnweight lower length positive bounded mode field)‖ ≤ ‖field‖ :=
    massBound.trans (by simpa only [one_mul] using massInput)
  nlinarith [norm_nonneg field,
    norm_nonneg (annularModeDerivative lower field), norm_nonneg (annularModeMass lower field),
    norm_nonneg (annularModeOuter lower field),
    norm_nonneg (annularModeDerivative lower (highModeEnergyUnweight lower length positive bounded mode field)),
    norm_nonneg (annularModeMass lower (highModeEnergyUnweight lower length positive bounded mode field)),
    sq_nonneg (‖field‖ - ‖annularModeOuter lower field‖),
    norm_nonneg (highModeEnergyUnweight lower length positive bounded mode field)]

theorem highNegativePower_one_le (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    1 ≤ lower ^ (-highTiltExponent) := by
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_of_nonpos positive bounded (neg_nonpos.mpr highTiltExponent_pos.le)

theorem highModeEnergyWeight_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    ‖highModeEnergyWeight lower length positive bounded mode field‖ ≤
      (3 * lower ^ (-highTiltExponent)) * ‖field‖ := by
  let scale := lower ^ (-highTiltExponent)
  have scaleNonnegative : 0 ≤ scale := (Real.rpow_pos_of_pos positive _).le
  have scaleOne : 1 ≤ scale := highNegativePower_one_le lower positive bounded
  have inputSq := annularModeEnergy_norm_sq lower field
  have outputSq := annularModeEnergy_norm_sq lower
    (highModeEnergyWeight lower length positive bounded mode field)
  have derivative := highModeEnergyWeight_derivative lower length positive bounded mode field
  have derivativeBound : ‖annularModeDerivative lower
      (highModeEnergyWeight lower length positive bounded mode field)‖ ≤
      scale * ‖annularModeDerivative lower field‖ +
        (highTiltExponent / 3 * scale) * ‖annularModeMass lower field‖ := by
    rw [derivative]
    exact (norm_add_le _ _).trans (add_le_add
      (scalarRadialMap_bound lower (highPowerCurve lower (-highTiltExponent) positive) scale
        (highNegativePower_bound lower positive bounded) (annularModeDerivative lower field))
      (scalarRadialMap_bound lower (highEnergySlopeRatio lower length (-highTiltExponent) positive mode)
        (highTiltExponent / 3 * scale) (highEnergyNegativeSlope_bound lower length positive bounded mode)
        (annularModeMass lower field)))
  have massBound : ‖annularModeMass lower
      (highModeEnergyWeight lower length positive bounded mode field)‖ ≤
      scale * ‖annularModeMass lower field‖ := by
    rw [highModeEnergyWeight_mass]
    exact scalarRadialMap_bound lower (highPowerCurve lower (-highTiltExponent) positive) scale
      (highNegativePower_bound lower positive bounded) (annularModeMass lower field)
  have outerEq := highModeEnergyWeight_outer lower length positive bounded mode field
  have derivativeInput := annularModeDerivative_bound lower field
  have massInput := annularModeMass_bound lower field
  have outerInput := annularModeOuter_bound lower field
  have exponentRatio : highTiltExponent / 3 = 3 / 4 := by norm_num [highTiltExponent]
  rw [exponentRatio] at derivativeBound
  rw [outerEq] at outputSq
  dsimp [scale] at *
  have derivativeBound' : ‖annularModeDerivative lower
      (highModeEnergyWeight lower length positive bounded mode field)‖ ≤
      2 * (lower ^ (-highTiltExponent) * ‖field‖) := by
    calc
      _ ≤ lower ^ (-highTiltExponent) * ‖annularModeDerivative lower field‖ +
          (3 / 4 * lower ^ (-highTiltExponent)) * ‖annularModeMass lower field‖ := derivativeBound
      _ ≤ lower ^ (-highTiltExponent) * ‖field‖ +
          (3 / 4 * lower ^ (-highTiltExponent)) * ‖field‖ := by
        gcongr
        · simpa only [one_mul] using derivativeInput
        · simpa only [one_mul] using massInput
      _ ≤ 2 * (lower ^ (-highTiltExponent) * ‖field‖) := by
        nlinarith [norm_nonneg field, Real.rpow_pos_of_pos positive (-highTiltExponent)]
  have massBound' : ‖annularModeMass lower
      (highModeEnergyWeight lower length positive bounded mode field)‖ ≤
      lower ^ (-highTiltExponent) * ‖field‖ :=
    massBound.trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using massInput)
      (Real.rpow_pos_of_pos positive _).le)
  have outerBound' : ‖annularModeOuter lower field‖ ≤
      lower ^ (-highTiltExponent) * ‖field‖ := by
    calc
      _ ≤ ‖field‖ := by simpa only [one_mul] using outerInput
      _ ≤ lower ^ (-highTiltExponent) * ‖field‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right scaleOne (norm_nonneg field)
  let transformed := highModeEnergyWeight lower length positive bounded mode field
  let target := lower ^ (-highTiltExponent) * ‖field‖
  let derivativeNorm := ‖annularModeDerivative lower transformed‖
  let massNorm := ‖annularModeMass lower transformed‖
  let outerNorm := ‖annularModeOuter lower transformed‖
  have frozenSq : ‖transformed‖ ^ 2 = derivativeNorm ^ 2 + massNorm ^ 2 + outerNorm ^ 2 := by
    simpa only [derivativeNorm, massNorm, outerNorm] using annularModeEnergy_norm_sq lower transformed
  have frozenDerivative : derivativeNorm ≤ 2 * target := by
    simpa only [derivativeNorm, target, transformed] using derivativeBound'
  have frozenMass : massNorm ≤ target := by
    simpa only [massNorm, target, transformed] using massBound'
  have frozenOuter : outerNorm ≤ target := by
    simpa only [outerNorm, target, transformed, highModeEnergyWeight_outer] using outerBound'
  have targetNonnegative : 0 ≤ target :=
    mul_nonneg (Real.rpow_pos_of_pos positive _).le (norm_nonneg field)
  have frozen : ‖transformed‖ ≤ 3 * target := by
    nlinarith [norm_nonneg transformed, norm_nonneg (annularModeDerivative lower transformed),
      norm_nonneg (annularModeMass lower transformed), norm_nonneg (annularModeOuter lower transformed)]
  simpa only [transformed, target, mul_assoc] using frozen

def highEnergyUnweightAmbient (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularEnergyAmbient lower →L[ℂ] AnnularEnergyAmbient lower :=
  complexLpTwoMap (highModeEnergyUnweight lower length positive bounded) 3 (by norm_num)
    (highModeEnergyUnweight_bound lower length positive bounded)

def highEnergyWeightAmbient (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularEnergyAmbient lower →L[ℂ] AnnularEnergyAmbient lower :=
  complexLpTwoMap (highModeEnergyWeight lower length positive bounded)
    (3 * lower ^ (-highTiltExponent))
    (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos positive _).le)
    (highModeEnergyWeight_bound lower length positive bounded)

def highPowerFiniteCore (lower power : ℝ) (positive : 0 < lower) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ]
      (HighAnnularMode →₀ complexSmoothRadialCore 1) :=
  Finsupp.mapRange.linearMap (highPowerComplexCore lower power positive)

@[simp] theorem highPowerFiniteCore_apply (lower power : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    highPowerFiniteCore lower power positive core mode =
      highPowerComplexCore lower power positive (core mode) := rfl

theorem highEnergyUnweightAmbient_core (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyUnweightAmbient lower length positive bounded
      (finiteAnnularEnergyCore lower length positive core) =
    finiteAnnularEnergyCore lower length positive
      (highPowerFiniteCore lower highTiltExponent positive core) := by
  apply lp.ext
  funext mode
  change highModeEnergyUnweight lower length positive bounded mode
      (finiteAnnularEnergyCore lower length positive core mode) =
    finiteAnnularEnergyCore lower length positive
      (highPowerFiniteCore lower highTiltExponent positive core) mode
  rw [finiteEnergy_mode, finiteEnergy_mode, highPowerFiniteCore_apply,
    highModeEnergyUnweight_core]

theorem highEnergyWeightAmbient_core (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyWeightAmbient lower length positive bounded
      (finiteAnnularEnergyCore lower length positive core) =
    finiteAnnularEnergyCore lower length positive
      (highPowerFiniteCore lower (-highTiltExponent) positive core) := by
  apply lp.ext
  funext mode
  change highModeEnergyWeight lower length positive bounded mode
      (finiteAnnularEnergyCore lower length positive core mode) =
    finiteAnnularEnergyCore lower length positive
      (highPowerFiniteCore lower (-highTiltExponent) positive core) mode
  rw [finiteEnergy_mode, finiteEnergy_mode, highPowerFiniteCore_apply,
    highModeEnergyWeight_core]

theorem highEnergyUnweight_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) :
    highEnergyUnweightAmbient lower length positive bounded field.val ∈
      annularEnergySpace lower length positive := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    ((LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      ((highEnergyUnweightAmbient lower length positive bounded).continuous.comp continuous_subtype_val)) _ field
  intro core
  change highEnergyUnweightAmbient lower length positive bounded
    (finiteAnnularEnergyCore lower length positive core) ∈ _
  rw [highEnergyUnweightAmbient_core]
  exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩

theorem highEnergyWeight_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) :
    highEnergyWeightAmbient lower length positive bounded field.val ∈
      annularEnergySpace lower length positive := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    ((LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      ((highEnergyWeightAmbient lower length positive bounded).continuous.comp continuous_subtype_val)) _ field
  intro core
  change highEnergyWeightAmbient lower length positive bounded
    (finiteAnnularEnergyCore lower length positive core) ∈ _
  rw [highEnergyWeightAmbient_core]
  exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩

def highEnergyUnweight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  ((highEnergyUnweightAmbient lower length positive bounded).comp
    (annularEnergySpace lower length positive).subtypeL).codRestrict _
      (highEnergyUnweight_mem lower length positive bounded)

def highEnergyWeight (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  ((highEnergyWeightAmbient lower length positive bounded).comp
    (annularEnergySpace lower length positive).subtypeL).codRestrict _
      (highEnergyWeight_mem lower length positive bounded)

end Grad.AnnularHighTilt
