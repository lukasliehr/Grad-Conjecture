import AAG5ActualEnergyCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularVariational Grad.CircularHighWeak

/-- Recover the conjugated field from the actual potential coordinate. -/
def annularValueMassRatio (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹,
    (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous.inv₀
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem annularValueMassRatio_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularValueMassRatio lower length positive mode radius| ≤ 1 / 3 := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have nine := annularPotential_nine_le length radius mode.val.1 mode.val.2 mode.property
    (positive.trans_le inside.1) inside.2
  have rootBound : 3 ≤ annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius := by
    nlinarith
  change |(annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹| ≤ _
  rw [abs_inv, abs_of_pos rootPositive, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) rootBound

/-- The exact multiplier 2/(r sqrt(V)) on the annulus. -/
def annularRadialMassRatio (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => 2 / max lower radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    (continuous_const.div (continuous_const.max continuous_id)
      (fun radius => (positive.trans_le (le_max_left lower radius)).ne')).div
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem annularRadialMassRatio_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularRadialMassRatio lower length positive mode radius| ≤ 2 / 3 := by
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
  have productBound : 3 ≤
      radius * annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius := by
    nlinarith
  change |2 / max lower radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ _
  rw [max_eq_right inside.1, div_div, abs_of_pos (div_pos (by norm_num) productPositive)]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) productBound

def annularValueMassMap (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
    (annularValueMassRatio_bound lower length positive mode)

def annularRadialMassMap (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  scalarRadialMap lower (annularRadialMassRatio lower length positive mode) (2 / 3)
    (annularRadialMassRatio_bound lower length positive mode)

theorem annularValueMassMap_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularValueMassMap lower length positive mode field‖ ≤ (1 / 3 : ℝ) * ‖field‖ :=
  scalarRadialMap_bound _ _ _ _ field

theorem annularRadialMassMap_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularRadialMassMap lower length positive mode field‖ ≤ (2 / 3 : ℝ) * ‖field‖ :=
  scalarRadialMap_bound _ _ _ _ field

def annularEnergyValue (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (annularValueMassMap lower length positive) (1 / 3) (by norm_num)
    (annularValueMassMap_bound lower length positive)).comp
      (annularEnergyMass lower length positive)

def annularEnergyRadial (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (annularRadialMassMap lower length positive) (2 / 3) (by norm_num)
    (annularRadialMassMap_bound lower length positive)).comp
      (annularEnergyMass lower length positive)

theorem annularEnergyValue_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyValue lower length positive field‖ ≤ (1 / 3 : ℝ) * ‖field‖ :=
  (complexLpTwoMap_bound (annularValueMassMap lower length positive) (1 / 3) (by norm_num)
    (annularValueMassMap_bound lower length positive) (annularEnergyMass lower length positive field)).trans
      (mul_le_mul_of_nonneg_left (annularEnergyMass_bound lower length positive field) (by norm_num))

theorem annularEnergyRadial_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyRadial lower length positive field‖ ≤ (2 / 3 : ℝ) * ‖field‖ :=
  (complexLpTwoMap_bound (annularRadialMassMap lower length positive) (2 / 3) (by norm_num)
    (annularRadialMassMap_bound lower length positive) (annularEnergyMass lower length positive field)).trans
      (mul_le_mul_of_nonneg_left (annularEnergyMass_bound lower length positive field) (by norm_num))

theorem scalarRadialMap_weightedCurve (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound)
    (curve : C(ℝ, ComplexEuclidean 1)) :
    scalarRadialMap lower coefficient bound bounded (weightedCurveComplex 1 lower curve) =
      weightedCurveComplex 1 lower (continuousCurveWeight 1 coefficient curve) := by
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower coefficient bound bounded (weightedCurveComplex 1 lower curve),
    radialToLp_ae lower curve curve.continuous,
    radialToLp_ae lower (continuousCurveWeight 1 coefficient curve)
      (continuousCurveWeight 1 coefficient curve).continuous] with radius mapping value weighted
  rw [mapping]
  change coefficient radius • radialToLp lower curve curve.continuous radius =
    radialToLp lower (continuousCurveWeight 1 coefficient curve)
      (continuousCurveWeight 1 coefficient curve).continuous radius
  rw [value, weighted]
  exact smul_comm (coefficient radius) (Real.sqrt radius) (curve radius)

end Grad.AnnularReconstruction
