import AAR8OriginalPhysicalFirstRow
import AAG13PhysicalTestMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarScalar_inner (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (test field : CollarL2 (ComplexEuclidean 1) lower) :
    inner ℂ (collarScalar 1 lower coefficient test) field =
      inner ℂ test (collarScalar 1 lower coefficient field) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [collarScalar_ae 1 lower coefficient test, collarScalar_ae 1 lower coefficient field]
    with radius testLaw fieldLaw
  rw [testLaw, fieldLaw, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

theorem collarScalar_weightedCurve (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (curve : C(ℝ, ComplexEuclidean 1)) :
    collarScalar 1 lower coefficient (weightedCurveComplex 1 lower curve) =
      weightedCurveComplex 1 lower (continuousCurveWeight 1 coefficient curve) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower coefficient (weightedCurveComplex 1 lower curve),
    radialToLp_ae lower curve curve.continuous,
    radialToLp_ae lower (continuousCurveWeight 1 coefficient curve)
      (continuousCurveWeight 1 coefficient curve).continuous] with radius scalar original weighted
  change weightedCurveComplex 1 lower curve radius = _ at original
  change weightedCurveComplex 1 lower (continuousCurveWeight 1 coefficient curve) radius = _ at weighted
  rw [scalar, original, weighted]
  exact smul_comm _ _ _

def annularRadiusCurve : C(ℝ, ℝ) := ⟨id, continuous_id⟩

/-- Literal r dr pairing after decoding the square-root storage. -/
theorem weightedCurve_test_inner (lower : ℝ) (positive : 0 < lower)
    (test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1) (field : RadialL2 1 lower) :
    inner ℂ (weightedCurveComplex 1 lower (collarTestCurve test vector)) field =
      collarPairing lower (annularRadiusCurve * test) vector (radialOrdinary 1 lower positive field) := by
  rw [L2.inner_def, collarPairing_integral]
  apply integral_congr_ae
  filter_upwards [radialToLp_ae lower (collarTestCurve test vector) (collarTestCurve test vector).continuous,
    radialOrdinary_ae 1 lower positive field, ae_restrict_mem measurableSet_Icc]
    with radius stored decoded inside
  change weightedCurveComplex 1 lower (collarTestCurve test vector) radius = _ at stored
  rw [stored, decoded, inner_smul_left_eq_smul]
  change Real.sqrt radius • inner ℂ (test radius • vector) (field radius) =
    (radius * test radius) • inner ℂ vector (reciprocalRadialWeight lower (fun _ => 1) radius • field radius)
  rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul, smul_smul]
  change (Real.sqrt radius * test radius) • inner ℂ vector (field radius) =
    ((radius * test radius) * reciprocalRadialWeight lower (fun _ => 1) radius) • inner ℂ vector (field radius)
  congr 1
  rw [reciprocalRadialWeight, max_eq_right inside.1, one_div]
  have rootNonzero := (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne'
  have square := Real.sq_sqrt (positive.trans_le inside.1).le
  field_simp
  rw [square]
  ring

theorem annularEnergyMass_mode (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyMass lower length positive field mode =
      collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (annularEnergyValue lower length positive field mode) := by
  let mass := annularEnergyMass lower length positive field mode
  change mass = collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
    (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass)
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
    (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass] with radius scalar value
  rw [scalar, value]
  change mass radius = annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius •
    ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • mass radius)
  rw [smul_smul, mul_inv_cancel₀ (annularPotentialWeight_pos lower length positive mode radius).ne', one_smul]

theorem annularImaginarySymbolMap_value (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (symbol : ℝ)
    (dominated : ∀ radius ∈ Icc lower 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2)
    (mass : RadialL2 1 lower) :
    annularImaginarySymbolMap lower length positive mode symbol dominated mass =
      (Complex.I * (symbol : ℂ)) • annularValueMassMap lower length positive mode mass := by
  change Complex.I • scalarRadialMap lower (annularSymbolRatio lower length positive mode symbol) 1
    (annularSymbolRatio_bound lower length positive mode symbol dominated) mass = _
  have realLaw : scalarRadialMap lower (annularSymbolRatio lower length positive mode symbol) 1
      (annularSymbolRatio_bound lower length positive mode symbol dominated) mass =
      (symbol : ℂ) • annularValueMassMap lower length positive mode mass := by
    apply Lp.ext
    filter_upwards [scalarRadialMap_ae lower (annularSymbolRatio lower length positive mode symbol) 1
        (annularSymbolRatio_bound lower length positive mode symbol dominated) mass,
      scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass,
      Lp.coeFn_smul (symbol : ℂ) (annularValueMassMap lower length positive mode mass)]
      with radius actual value scaled
    rw [actual, scaled, Pi.smul_apply]
    change (symbol / annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) • mass radius =
      (symbol : ℂ) • annularValueMassMap lower length positive mode mass radius
    change annularValueMassMap lower length positive mode mass radius = _ at value
    rw [value, div_eq_mul_inv, mul_smul]
    rfl
  rw [realLaw, smul_smul]

theorem annularEnergyD_mode (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyD lower length positive field mode =
      annularDSymbol mode • annularEnergyValue lower length positive field mode :=
  annularImaginarySymbolMap_value lower length positive mode _
    (annularDSymbol_dominated lower length positive mode) _

def annularCellSymbol (length : ℝ) (mode : HighAnnularMode) : ℂ :=
  Complex.I * ((Grad.CircularHighWeak.highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length : ℝ) : ℂ)

theorem annularEnergyCell_mode (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyCell lower length positive field mode =
      annularCellSymbol length mode • annularEnergyValue lower length positive field mode :=
  annularImaginarySymbolMap_value lower length positive mode _
    (annularCellSymbol_dominated lower length positive mode) _

end Grad.AnnularReconstruction
