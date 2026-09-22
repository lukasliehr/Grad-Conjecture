import AAR6PhysicalWeakDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarScalar_mul_apply (lower : ℝ) (first second : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower first (collarScalar 1 lower second field) =
      collarScalar 1 lower (first * second) field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower first (collarScalar 1 lower second field),
    collarScalar_ae 1 lower second field, collarScalar_ae 1 lower (first * second) field]
    with radius outer inner product
  rw [outer, inner, product, smul_smul]
  rfl

theorem collarScalar_comm (lower : ℝ) (first second : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower first (collarScalar 1 lower second field) =
      collarScalar 1 lower second (collarScalar 1 lower first field) := by
  rw [collarScalar_mul_apply, collarScalar_mul_apply, mul_comm first second]

theorem radialOrdinary_collarScalar (lower : ℝ) (positive : 0 < lower) (coefficient : C(ℝ, ℝ))
    (field : RadialL2 1 lower) :
    radialOrdinary 1 lower positive (collarScalar 1 lower coefficient field) =
      collarScalar 1 lower coefficient (radialOrdinary 1 lower positive field) :=
  collarScalar_comm lower _ coefficient field

theorem annularEnergyValue_ordinary (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    radialOrdinary 1 lower positive (annularEnergyValue lower length positive field mode) =
      annularOrdinaryCoordinate lower length positive bounded mode 0 field := by
  have stored := weightedRadialCoordinate_eq_sqrt 1 lower positive bounded 0
    (annularModeRadialH1 lower length positive mode field)
  rw [annularModeRadialH1_value] at stored
  exact (congrArg (radialOrdinary 1 lower positive) stored).trans (radialOrdinary_sqrt 1 lower positive _)

theorem annularEnergyDerivative_ordinary (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    radialOrdinary 1 lower positive (annularEnergyDerivative lower length positive field mode) =
      annularOrdinaryCoordinate lower length positive bounded mode 1 field := by
  have stored := weightedRadialCoordinate_eq_sqrt 1 lower positive bounded 1
    (annularModeRadialH1 lower length positive mode field)
  rw [annularModeRadialH1_derivative] at stored
  exact (congrArg (radialOrdinary 1 lower positive) stored).trans (radialOrdinary_sqrt 1 lower positive _)

def annularPhaseCurve (parameters : PhaseParameters) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨annularPhaseSlope parameters cell, annularPhaseSlope_continuous parameters cell⟩

def annularRadialCurve (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => 2 / max lower radius,
    continuous_const.div (continuous_const.max continuous_id)
      (fun radius => (positive.trans_le (le_max_left lower radius)).ne')⟩

theorem annularEnergyPhase_mode (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field mode =
      collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
        (annularEnergyValue lower length positive field mode) := by
  let mass := annularEnergyMass lower length positive field mode
  change scalarRadialMap lower (annularPhaseMassRatio parameters lower length positive mode) (1 / 2)
      (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) mass =
    collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass)
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower (annularPhaseMassRatio parameters lower length positive mode) (1 / 2)
      (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) mass,
    collarScalar_ae 1 lower (annularPhaseCurve parameters mode.val.2)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass] with radius phase scalar value
  rw [phase, scalar, value]
  change (annularPhaseSlope parameters mode.val.2 radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) • mass radius =
    annularPhaseSlope parameters mode.val.2 radius •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • mass radius)
  rw [div_eq_mul_inv, mul_smul]

theorem annularEnergyRadial_mode (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyRadial lower length positive field mode =
      collarScalar 1 lower (annularRadialCurve lower positive)
        (annularEnergyValue lower length positive field mode) := by
  let mass := annularEnergyMass lower length positive field mode
  change scalarRadialMap lower (annularRadialMassRatio lower length positive mode) (2 / 3)
      (annularRadialMassRatio_bound lower length positive mode) mass =
    collarScalar 1 lower (annularRadialCurve lower positive)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass)
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower (annularRadialMassRatio lower length positive mode) (2 / 3)
      (annularRadialMassRatio_bound lower length positive mode) mass,
    collarScalar_ae 1 lower (annularRadialCurve lower positive)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass] with radius radial scalar value
  rw [radial, scalar, value]
  change (2 / max lower radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) • mass radius =
    (2 / max lower radius) •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • mass radius)
  rw [div_eq_mul_inv (2 / max lower radius), mul_smul]

def annularDecodeMode (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : RadialL2 1 lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarScalar 1 lower (annularInversePhase parameters mode.val.2)).comp
    (radialOrdinary 1 lower positive)

theorem annularPhysicalValue_eq_decode (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    annularPhysicalValue parameters lower length positive bounded mode field =
      annularDecodeMode parameters lower positive mode (annularEnergyValue lower length positive field mode) := by
  change collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (annularOrdinaryCoordinate lower length positive bounded mode 0 field) =
    collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (radialOrdinary 1 lower positive (annularEnergyValue lower length positive field mode))
  rw [annularEnergyValue_ordinary lower length positive bounded mode field]

end Grad.AnnularReconstruction
