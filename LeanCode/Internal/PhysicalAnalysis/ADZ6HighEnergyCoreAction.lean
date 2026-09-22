import ADZ5HighEnergyModeTilt

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction

@[simp] theorem highModeEnergyUnweight_derivative (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeDerivative lower (highModeEnergyUnweight lower length positive bounded mode field) =
      scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
          (highPositivePower_bound lower positive bounded) (annularModeDerivative lower field) +
        scalarRadialMap lower (highEnergySlopeRatio lower length highTiltExponent positive mode)
          (highTiltExponent / 3) (highEnergyPositiveSlope_bound lower length positive bounded mode)
          (annularModeMass lower field) := rfl

@[simp] theorem highModeEnergyUnweight_mass (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeMass lower (highModeEnergyUnweight lower length positive bounded mode field) =
      scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded) (annularModeMass lower field) := rfl

@[simp] theorem highModeEnergyUnweight_outer (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeOuter lower (highModeEnergyUnweight lower length positive bounded mode field) =
      annularModeOuter lower field := rfl

@[simp] theorem highModeEnergyWeight_derivative (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeDerivative lower (highModeEnergyWeight lower length positive bounded mode field) =
      scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
          (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
          (annularModeDerivative lower field) +
        scalarRadialMap lower (highEnergySlopeRatio lower length (-highTiltExponent) positive mode)
          (highTiltExponent / 3 * lower ^ (-highTiltExponent))
          (highEnergyNegativeSlope_bound lower length positive bounded mode) (annularModeMass lower field) := rfl

@[simp] theorem highModeEnergyWeight_mass (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeMass lower (highModeEnergyWeight lower length positive bounded mode field) =
      scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
        (annularModeMass lower field) := rfl

@[simp] theorem highModeEnergyWeight_outer (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (field : AnnularModeEnergyAmbient lower) :
    annularModeOuter lower (highModeEnergyWeight lower length positive bounded mode field) =
      annularModeOuter lower field := rfl

private theorem highModeEnergyPower_core (lower length power valueBound slopeBound : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode)
    (valueLaw : ∀ radius ∈ Icc lower 1, |highPowerCurve lower power positive radius| ≤ valueBound)
    (slopeLaw : ∀ radius ∈ Icc lower 1,
      |highEnergySlopeRatio lower length power positive mode radius| ≤ slopeBound)
    (map : AnnularModeEnergyAmbient lower →L[ℂ] AnnularModeEnergyAmbient lower)
    (derivativeLaw : ∀ field, annularModeDerivative lower (map field) =
      scalarRadialMap lower (highPowerCurve lower power positive) valueBound valueLaw
          (annularModeDerivative lower field) +
        scalarRadialMap lower (highEnergySlopeRatio lower length power positive mode) slopeBound slopeLaw
          (annularModeMass lower field))
    (massLaw : ∀ field, annularModeMass lower (map field) =
      scalarRadialMap lower (highPowerCurve lower power positive) valueBound valueLaw
        (annularModeMass lower field))
    (outerLaw : ∀ field, annularModeOuter lower (map field) = annularModeOuter lower field)
    (core : complexSmoothRadialCore 1) :
    map (annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core) =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2
        (highPowerComplexCore lower power positive core) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · change annularModeDerivative lower (map (annularModeEnergyCore lower length positive
      mode.val.1 mode.val.2 core)) = _
    rw [derivativeLaw]
    change scalarRadialMap lower (highPowerCurve lower power positive) valueBound valueLaw
          (weightedCurveComplex 1 lower core.val.2) +
        scalarRadialMap lower (highEnergySlopeRatio lower length power positive mode) slopeBound slopeLaw
          (weightedCurveComplex 1 lower (continuousCurveWeight 1
            (annularPotentialWeight lower length positive mode.val.1 mode.val.2) core.val.1)) =
      weightedCurveComplex 1 lower (highPowerComplexCore lower power positive core).val.2
    rw [scalarRadialMap_weightedCurve, scalarRadialMap_weightedCurve, ← map_add]
    congr 1
    apply ContinuousMap.ext
    intro radius
    rw [highPowerComplexCore_slope]
    change (highPowerCurve lower power positive radius : ℂ) • core.val.2 radius +
      ((highPowerSlopeCurve lower power positive radius /
        annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius : ℝ) : ℂ) •
          ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius : ℂ) •
            core.val.1 radius) = _
    rw [smul_smul]
    congr 1
    push_cast
    field_simp [(annularPotentialWeight_pos lower length positive mode radius).ne']
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    apply Prod.ext
    · change annularModeMass lower (map (annularModeEnergyCore lower length positive
        mode.val.1 mode.val.2 core)) = _
      rw [massLaw]
      change scalarRadialMap lower (highPowerCurve lower power positive) valueBound valueLaw
          (weightedCurveComplex 1 lower (continuousCurveWeight 1
            (annularPotentialWeight lower length positive mode.val.1 mode.val.2) core.val.1)) =
        weightedCurveComplex 1 lower (continuousCurveWeight 1
          (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
          (highPowerComplexCore lower power positive core).val.1)
      rw [scalarRadialMap_weightedCurve]
      congr 1
      apply ContinuousMap.ext
      intro radius
      change (highPowerCurve lower power positive radius : ℂ) •
          ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius : ℂ) •
            core.val.1 radius) =
        (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius : ℂ) •
          ((highPowerCurve lower power positive radius : ℂ) • core.val.1 radius)
      simp only [smul_smul]
      congr 1
      ring
    · change annularModeOuter lower (map (annularModeEnergyCore lower length positive
        mode.val.1 mode.val.2 core)) = _
      rw [outerLaw]
      change (Real.sqrt 2 : ℂ) • core.val.1 1 =
        (Real.sqrt 2 : ℂ) • ((highPowerCurve lower power positive 1 : ℂ) • core.val.1 1)
      rw [highPower_outer lower power positive bounded]
      simp

theorem highModeEnergyUnweight_core (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    highModeEnergyUnweight lower length positive bounded mode
      (annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core) =
    annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (highPowerComplexCore lower highTiltExponent positive core) :=
  highModeEnergyPower_core lower length highTiltExponent 1 (highTiltExponent / 3)
    positive bounded mode (highPositivePower_bound lower positive bounded)
    (highEnergyPositiveSlope_bound lower length positive bounded mode)
    (highModeEnergyUnweight lower length positive bounded mode)
    (highModeEnergyUnweight_derivative lower length positive bounded mode)
    (highModeEnergyUnweight_mass lower length positive bounded mode)
    (highModeEnergyUnweight_outer lower length positive bounded mode) core

theorem highModeEnergyWeight_core (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    highModeEnergyWeight lower length positive bounded mode
      (annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core) =
    annularModeEnergyCore lower length positive mode.val.1 mode.val.2
      (highPowerComplexCore lower (-highTiltExponent) positive core) :=
  highModeEnergyPower_core lower length (-highTiltExponent) (lower ^ (-highTiltExponent))
    (highTiltExponent / 3 * lower ^ (-highTiltExponent)) positive bounded mode
    (highNegativePower_bound lower positive bounded)
    (highEnergyNegativeSlope_bound lower length positive bounded mode)
    (highModeEnergyWeight lower length positive bounded mode)
    (highModeEnergyWeight_derivative lower length positive bounded mode)
    (highModeEnergyWeight_mass lower length positive bounded mode)
    (highModeEnergyWeight_outer lower length positive bounded mode) core

end Grad.AnnularHighTilt
