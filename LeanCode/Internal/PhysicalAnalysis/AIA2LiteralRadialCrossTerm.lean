import AIA1CompletedRadialEndpointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularConverse Grad.AnnularReconstruction
open Grad.AnnularCurrentEnergy Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The original r dr storage cancels exactly against the single 1/r in the cross term. -/
theorem radialSqrt_reciprocal_inner (lower : ℝ) (positive : 0 < lower)
    (test field : CollarL2 (ComplexEuclidean 1) lower) :
    inner ℂ (radialSqrtMap 1 lower test)
      (collarScalar 1 lower (highReciprocalRadius lower positive) (radialSqrtMap 1 lower field)) =
      inner ℂ test field := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialSqrtMap_ae 1 lower test, radialSqrtMap_ae 1 lower field,
    collarScalar_ae 1 lower (highReciprocalRadius lower positive) (radialSqrtMap 1 lower field),
    ae_restrict_mem measurableSet_Icc] with radius testLaw fieldLaw scalarLaw inside
  rw [testLaw, scalarLaw, fieldLaw, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    inner_smul_right_eq_smul, smul_smul, smul_smul]
  change (Real.sqrt radius * (max lower radius)⁻¹ * Real.sqrt radius) • inner ℂ (test radius) (field radius) = _
  have radiusPositive := positive.trans_le inside.1
  have factor : Real.sqrt radius * (max lower radius)⁻¹ * Real.sqrt radius = 1 := by
    rw [max_eq_right inside.1]
    calc
      _ = (Real.sqrt radius) ^ 2 * radius⁻¹ := by ring
      _ = 1 := by rw [Real.sq_sqrt radiusPositive.le, mul_inv_cancel₀ radiusPositive.ne']
  rw [factor, one_smul]

/-- Exact completed reciprocal-radius cross identity before phase conjugation. -/
theorem weightedRadial_reciprocal_parts (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (test field : WeightedRadialH1 1 lower) :
    inner ℂ (weightedRadialCoordinate 1 lower 1 test)
      (collarScalar 1 lower (highReciprocalRadius lower positive) (weightedRadialCoordinate 1 lower 0 field)) +
    inner ℂ (collarScalar 1 lower (highReciprocalRadius lower positive) (weightedRadialCoordinate 1 lower 0 test))
      (weightedRadialCoordinate 1 lower 1 field) =
    inner ℂ (weightedRadialTrace 1 lower positive bounded 1 test)
      (weightedRadialTrace 1 lower positive bounded 1 field) -
    inner ℂ (weightedRadialTrace 1 lower positive bounded 0 test)
      (weightedRadialTrace 1 lower positive bounded 0 field) := by
  rw [collarScalar_inner]
  simp_rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le]
  rw [radialSqrt_reciprocal_inner, radialSqrt_reciprocal_inner]
  exact weightedRadial_completed_parts 1 lower positive bounded test field

/-- The SAME completed energy mode therefore has the literal endpoint cross term. -/
theorem annularEnergy_mode_cross (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (test field : annularEnergySpace lower length positive) :
    inner ℂ (annularEnergyDerivative lower length positive test mode)
      (highEnergyRadius lower length positive field mode) +
    inner ℂ (highEnergyRadius lower length positive test mode)
      (annularEnergyDerivative lower length positive field mode) =
    inner ℂ (weightedRadialTrace 1 lower positive bounded 1 (annularModeRadialH1 lower length positive mode test))
      (weightedRadialTrace 1 lower positive bounded 1 (annularModeRadialH1 lower length positive mode field)) -
    inner ℂ (weightedRadialTrace 1 lower positive bounded 0 (annularModeRadialH1 lower length positive mode test))
      (weightedRadialTrace 1 lower positive bounded 0 (annularModeRadialH1 lower length positive mode field)) := by
  simpa only [annularModeRadialH1_value, annularModeRadialH1_derivative, highEnergyRadius_mode] using
    weightedRadial_reciprocal_parts lower positive bounded
      (annularModeRadialH1 lower length positive mode test) (annularModeRadialH1 lower length positive mode field)

end Grad.AnnularCircularForm
