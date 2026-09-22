import AAR10ActualRadialPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularRadialMoment (lower : ℝ) (positive : 0 < lower) :
    RadialL2 1 lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarScalar 1 lower annularRadiusCurve).comp (radialOrdinary 1 lower positive)

theorem weightedCurve_test_moment (lower : ℝ) (positive : 0 < lower)
    (test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1) (field : RadialL2 1 lower) :
    inner ℂ (weightedCurveComplex 1 lower (collarTestCurve test vector)) field =
      collarPairing lower test vector (annularRadialMoment lower positive field) := by
  have literal := weightedCurve_test_inner lower positive test vector field
  change _ = collarPairing lower test vector
    (collarScalar 1 lower annularRadiusCurve (radialOrdinary 1 lower positive field))
  rw [collarScalar_pairing, mul_comm test annularRadiusCurve]
  exact literal

theorem annularRadialMoment_scalar (lower : ℝ) (positive : 0 < lower)
    (coefficient : C(ℝ, ℝ)) (field : RadialL2 1 lower) :
    annularRadialMoment lower positive (collarScalar 1 lower coefficient field) =
      collarScalar 1 lower coefficient (annularRadialMoment lower positive field) := by
  change collarScalar 1 lower annularRadiusCurve
    (radialOrdinary 1 lower positive (collarScalar 1 lower coefficient field)) = _
  rw [radialOrdinary_collarScalar, collarScalar_comm]
  rfl

theorem collarPairing_complex_smul (lower : ℝ) (test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1)
    (scalar : ℂ) (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarPairing lower test vector (scalar • field) = scalar * collarPairing lower test vector field := by
  change inner ℂ (collarContinuousL2 _ lower (collarTestCurve test vector)) (scalar • field) =
    scalar * inner ℂ (collarContinuousL2 _ lower (collarTestCurve test vector)) field
  exact inner_smul_right _ _ _

theorem collarScalar_const (lower scalar : ℝ) (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (ContinuousMap.const ℝ scalar) field = scalar • field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (ContinuousMap.const ℝ scalar) field,
    Lp.coeFn_smul scalar field] with radius literal scaled
  rw [literal, scaled, Pi.smul_apply]
  rfl

theorem collarScalar_radius_radial (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower annularRadiusCurve (collarScalar 1 lower (annularRadialCurve lower positive) field) =
      (2 : ℝ) • field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower annularRadiusCurve
      (collarScalar 1 lower (annularRadialCurve lower positive) field),
    collarScalar_ae 1 lower (annularRadialCurve lower positive) field,
    Lp.coeFn_smul (2 : ℝ) field, ae_restrict_mem measurableSet_Icc]
    with radius outer inner scaled inside
  rw [outer, inner, scaled, Pi.smul_apply]
  change radius • ((2 / max lower radius) • field radius) = (2 : ℝ) • field radius
  rw [smul_smul, max_eq_right inside.1]
  congr 1
  field_simp
  exact div_self (positive.trans_le inside.1).ne'

theorem annularRadialMoment_radial (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularRadialMoment lower positive (annularEnergyRadial lower length positive field mode) =
      (2 : ℝ) • annularOrdinaryCoordinate lower length positive bounded mode 0 field := by
  rw [annularEnergyRadial_mode]
  change collarScalar 1 lower annularRadiusCurve
    (radialOrdinary 1 lower positive (collarScalar 1 lower (annularRadialCurve lower positive)
      (annularEnergyValue lower length positive field mode))) = _
  rw [radialOrdinary_collarScalar, collarScalar_radius_radial,
    annularEnergyValue_ordinary lower length positive bounded mode field]

theorem collarWeakDerivative_radius (lower : ℝ)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    CollarWeakDerivative lower (collarScalar 1 lower annularRadiusCurve value)
      (value + collarScalar 1 lower annularRadiusCurve derivative) := by
  have product := collarWeakDerivative_scalar lower annularRadiusCurve (ContinuousMap.const ℝ 1)
    (fun radius => hasDerivAt_id radius) value derivative weak
  rw [collarScalar_const, one_smul] at product
  exact product

end Grad.AnnularReconstruction
