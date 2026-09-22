import AAZJ2ActualPhysicalJetSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity


/-- The graph's actual r dr coordinate is exactly the original stored
physical jet with only its analytic phase removed. -/
theorem annularPhysicalDecode_sqrt (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    radialSqrtMap 1 lower (annularDecodeMode parameters lower positive mode field) =
      collarScalar 1 lower (annularInversePhase parameters mode.val.2) field := by
  apply Lp.ext
  filter_upwards [radialSqrtMap_ae 1 lower (annularDecodeMode parameters lower positive mode field),
    collarScalar_ae 1 lower (annularInversePhase parameters mode.val.2) (radialOrdinary 1 lower positive field),
    radialOrdinary_ae 1 lower positive field,
    collarScalar_ae 1 lower (annularInversePhase parameters mode.val.2) field,
    ae_restrict_mem measurableSet_Icc] with radius sqrtLaw phaseLaw ordinaryLaw unphaseLaw inside
  rw [sqrtLaw, unphaseLaw]
  change Real.sqrt radius • collarScalar 1 lower (annularInversePhase parameters mode.val.2)
    (radialOrdinary 1 lower positive field) radius = _
  rw [phaseLaw, ordinaryLaw, smul_comm (Real.sqrt radius), smul_smul,
    reciprocalRadialWeight, max_eq_right inside.1, one_div, smul_smul, mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne', mul_one]

section Bounds
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))

theorem annularPhysicalJetGraph_coordinates (order : ℕ) (mode : HighAnnularMode) :
    weightedRadialCoordinate 1 lower 0 (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode) =
      collarScalar 1 lower (annularInversePhase parameters mode.val.2) (jet order mode) ∧
    weightedRadialCoordinate 1 lower 1 (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode) =
      collarScalar 1 lower (annularInversePhase parameters mode.val.2) (jet (order + 1) mode) := by
  constructor
  · rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, annularPhysicalJetGraph, compactWeakRadialGraph_value,
      annularPhysicalDecode_sqrt]
  · rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, annularPhysicalJetGraph, compactWeakRadialGraph_slope,
      annularPhysicalDecode_sqrt]

theorem annularPhysicalJetGraph_norm_le (order : ℕ) (mode : HighAnnularMode) :
    ‖annularPhysicalJetGraph parameters lower positive bounded jet weak order mode‖ ≤
      ‖jet order mode‖ + ‖jet (order + 1) mode‖ := by
  have square := weightedRadialH1_norm_sq 1 lower (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode)
  have coordinates := annularPhysicalJetGraph_coordinates parameters lower positive bounded jet weak order mode
  rw [coordinates.1, coordinates.2] at square
  have first := annularUnphase_norm_le parameters lower positive mode (jet order mode)
  have second := annularUnphase_norm_le parameters lower positive mode (jet (order + 1) mode)
  nlinarith [norm_nonneg (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode),
    norm_nonneg (jet order mode), norm_nonneg (jet (order + 1) mode),
    norm_nonneg (collarScalar 1 lower (annularInversePhase parameters mode.val.2) (jet order mode)),
    norm_nonneg (collarScalar 1 lower (annularInversePhase parameters mode.val.2) (jet (order + 1) mode)),
    mul_nonneg (norm_nonneg (jet order mode)) (norm_nonneg (jet (order + 1) mode))]

/-- Uniform control on the entire closed radial interval from two consecutive
actual physical jets. Together with two extra tangential grades this is the
summable majorant used for every mixed Fourier derivative. -/
theorem annularPhysicalJetSection_norm_le (order : ℕ) (mode : HighAnnularMode) :
    ‖annularPhysicalJetSection parameters lower positive bounded jet weak order mode‖ ≤
      sourceEndpointConstant lower * (‖jet order mode‖ + ‖jet (order + 1) mode‖) := by
  have sectionBound := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode)
  exact sectionBound.trans (mul_le_mul_of_nonneg_left
    (annularPhysicalJetGraph_norm_le parameters lower positive bounded jet weak order mode) (Real.sqrt_nonneg _))

end Bounds
end Grad.AnnularJointRegularity
