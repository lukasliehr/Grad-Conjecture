import ADZ8HighEnergyEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction

@[simp] theorem highEnergyUnweight_derivative_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyDerivative lower length positive
        (highEnergyUnweight lower length positive bounded field) mode =
      scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
          (highPositivePower_bound lower positive bounded)
          (annularEnergyDerivative lower length positive field mode) +
        scalarRadialMap lower
          (highEnergySlopeRatio lower length highTiltExponent positive mode)
          (highTiltExponent / 3) (highEnergyPositiveSlope_bound lower length positive bounded mode)
          (annularEnergyMass lower length positive field mode) := by
  change annularModeDerivative lower
      (highModeEnergyUnweight lower length positive bounded mode (field.val mode)) = _
  exact highModeEnergyUnweight_derivative lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyUnweight_mass_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyMass lower length positive
        (highEnergyUnweight lower length positive bounded field) mode =
      scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
        (highPositivePower_bound lower positive bounded)
        (annularEnergyMass lower length positive field mode) := by
  change annularModeMass lower
      (highModeEnergyUnweight lower length positive bounded mode (field.val mode)) = _
  exact highModeEnergyUnweight_mass lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyUnweight_outer_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyOuter lower length positive
      (highEnergyUnweight lower length positive bounded field) mode =
    annularEnergyOuter lower length positive field mode := by
  change annularModeOuter lower
      (highModeEnergyUnweight lower length positive bounded mode (field.val mode)) =
    annularModeOuter lower (field.val mode)
  exact highModeEnergyUnweight_outer lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyWeight_derivative_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyDerivative lower length positive
        (highEnergyWeight lower length positive bounded field) mode =
      scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
          (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
          (annularEnergyDerivative lower length positive field mode) +
        scalarRadialMap lower
          (highEnergySlopeRatio lower length (-highTiltExponent) positive mode)
          (highTiltExponent / 3 * lower ^ (-highTiltExponent))
          (highEnergyNegativeSlope_bound lower length positive bounded mode)
          (annularEnergyMass lower length positive field mode) := by
  change annularModeDerivative lower
      (highModeEnergyWeight lower length positive bounded mode (field.val mode)) = _
  exact highModeEnergyWeight_derivative lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyWeight_mass_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyMass lower length positive
        (highEnergyWeight lower length positive bounded field) mode =
      scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
        (annularEnergyMass lower length positive field mode) := by
  change annularModeMass lower
      (highModeEnergyWeight lower length positive bounded mode (field.val mode)) = _
  exact highModeEnergyWeight_mass lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyWeight_outer_apply (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    annularEnergyOuter lower length positive
      (highEnergyWeight lower length positive bounded field) mode =
    annularEnergyOuter lower length positive field mode := by
  change annularModeOuter lower
      (highModeEnergyWeight lower length positive bounded mode (field.val mode)) =
    annularModeOuter lower (field.val mode)
  exact highModeEnergyWeight_outer lower length positive bounded mode (field.val mode)

@[simp] theorem highEnergyUnweight_coreInto (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyUnweight lower length positive bounded
      (annularEnergyCoreInto lower length positive core) =
    annularEnergyCoreInto lower length positive
      (highPowerFiniteCore lower highTiltExponent positive core) := by
  apply Subtype.ext
  exact highEnergyUnweightAmbient_core lower length positive bounded core

@[simp] theorem highEnergyWeight_coreInto (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyWeight lower length positive bounded
      (annularEnergyCoreInto lower length positive core) =
    annularEnergyCoreInto lower length positive
      (highPowerFiniteCore lower (-highTiltExponent) positive core) := by
  apply Subtype.ext
  exact highEnergyWeightAmbient_core lower length positive bounded core

end Grad.AnnularHighTilt
