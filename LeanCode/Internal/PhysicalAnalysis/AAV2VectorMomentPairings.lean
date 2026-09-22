import AAV1VectorRadialIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

def vectorCollarPairing (lower : ℝ) (test : C(ℝ, ComplexEuclidean 1)) :
    CollarL2 (ComplexEuclidean 1) lower →L[ℂ] ℂ :=
  innerSL ℂ (collarContinuousL2 (ComplexEuclidean 1) lower test)

theorem weightedCurve_vector_moment (lower : ℝ) (positive : 0 < lower)
    (test : C(ℝ, ComplexEuclidean 1)) (field : RadialL2 1 lower) :
    inner ℂ (weightedCurveComplex 1 lower test) field =
      vectorCollarPairing lower test (annularRadialMoment lower positive field) := by
  change inner ℂ (weightedCurveComplex 1 lower test) field =
    inner ℂ (collarContinuousL2 (ComplexEuclidean 1) lower test)
      (collarScalar 1 lower annularRadiusCurve (radialOrdinary 1 lower positive field))
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialToLp_ae lower test test.continuous,
    (collarContinuous_memLp (ComplexEuclidean 1) lower test).coeFn_toLp,
    collarScalar_ae 1 lower annularRadiusCurve (radialOrdinary 1 lower positive field),
    radialOrdinary_ae 1 lower positive field, ae_restrict_mem measurableSet_Icc]
    with radius stored original radial decoded inside
  change weightedCurveComplex 1 lower test radius = _ at stored
  change collarContinuousL2 (ComplexEuclidean 1) lower test radius = _ at original
  rw [stored, original, radial, decoded, inner_smul_left_eq_smul,
    inner_smul_right_eq_smul, inner_smul_right_eq_smul, smul_smul]
  change Real.sqrt radius • inner ℂ (test radius) (field radius) =
    (radius * reciprocalRadialWeight lower (fun _ => 1) radius) • inner ℂ (test radius) (field radius)
  congr 1
  rw [reciprocalRadialWeight, max_eq_right inside.1, one_div]
  have rootNonzero := (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne'
  have square := Real.sq_sqrt (positive.trans_le inside.1).le
  field_simp
  exact square

theorem weightedCurve_vector_scalar (lower : ℝ) (positive : 0 < lower)
    (coefficient : C(ℝ, ℝ)) (test : C(ℝ, ComplexEuclidean 1)) (field : RadialL2 1 lower) :
    inner ℂ (collarScalar 1 lower coefficient (weightedCurveComplex 1 lower test)) field =
      vectorCollarPairing lower test
        (collarScalar 1 lower coefficient (annularRadialMoment lower positive field)) := by
  rw [collarScalar_inner, weightedCurve_vector_moment, annularRadialMoment_scalar]

theorem weightedCurve_vector_skew (lower : ℝ) (positive : 0 < lower)
    (symbol : ℂ) (skew : starRingEnd ℂ symbol = -symbol)
    (test : C(ℝ, ComplexEuclidean 1)) (field : RadialL2 1 lower) :
    inner ℂ (symbol • weightedCurveComplex 1 lower test) field =
      -vectorCollarPairing lower test (symbol • annularRadialMoment lower positive field) := by
  rw [inner_smul_left, skew, weightedCurve_vector_moment, map_smul, neg_mul]
  rfl

theorem annularMass_vector_pairing (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (test : C(ℝ, ComplexEuclidean 1))
    (field : annularEnergySpace lower length positive) :
    inner ℂ (weightedCurveComplex 1 lower
      (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2) test))
      (annularEnergyMass lower length positive field mode) =
      vectorCollarPairing lower test (collarScalar 1 lower (annularPotentialCurve lower length positive mode)
        (annularRadialMoment lower positive (annularEnergyValue lower length positive field mode))) := by
  rw [← collarScalar_weightedCurve, collarScalar_inner, annularEnergyMass_mode, collarScalar_mul_apply,
    weightedCurve_vector_moment, annularRadialMoment_scalar]
  rfl

end Grad.AnnularConverse
