import ANR25RadialWeakEquation
import ASG37ActualWeakRadialRepresentative

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace Grad.MatrixMultiplier

private theorem collarScalar_exists (dimension : ℕ) (lower : ℝ) (coefficient : C(ℝ, ℝ)) :
    ∃ mapping : CollarL2 (ComplexEuclidean dimension) lower →L[ℂ] CollarL2 (ComplexEuclidean dimension) lower,
      ∀ field, ∀ᵐ radius ∂volume.restrict (Icc lower 1),
        mapping field radius = coefficient radius • field radius := by
  let coefficients : ℝ → ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
    fun radius => coefficient radius • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)
  have continuous : Continuous coefficients := coefficient.continuous.smul continuous_const
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  have estimate : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ‖coefficients radius‖ ≤ bound := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    exact bounded radius inside
  refine ⟨matrixMultiplier (volume.restrict (Icc lower 1)) coefficients bound
    continuous.aestronglyMeasurable estimate, ?_⟩
  intro field
  exact matrixMultiplier_apply_ae _ coefficients bound continuous.aestronglyMeasurable estimate field

/-- Bounded multiplication on the unchanged ordinary collar L2 measure. -/
def collarScalar (dimension : ℕ) (lower : ℝ) (coefficient : C(ℝ, ℝ)) :
    CollarL2 (ComplexEuclidean dimension) lower →L[ℂ] CollarL2 (ComplexEuclidean dimension) lower :=
  (collarScalar_exists dimension lower coefficient).choose

theorem collarScalar_ae (dimension : ℕ) (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarScalar dimension lower coefficient field radius = coefficient radius • field radius :=
  (collarScalar_exists dimension lower coefficient).choose_spec field

theorem collarScalar_pairing (dimension : ℕ) (lower : ℝ) (coefficient test : C(ℝ, ℝ))
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower test vector (collarScalar dimension lower coefficient field) =
      collarPairing lower (test * coefficient) vector field := by
  rw [collarPairing_integral, collarPairing_integral]
  apply integral_congr_ae
  filter_upwards [collarScalar_ae dimension lower coefficient field] with radius literal
  rw [literal, inner_smul_right_eq_smul, smul_smul]
  rfl

/-- Decode the sqrt(r) storage of a radial coefficient without changing its field. -/
def radialOrdinary (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) :
    RadialL2 dimension lower →L[ℂ] CollarL2 (ComplexEuclidean dimension) lower :=
  collarScalar dimension lower ⟨reciprocalRadialWeight lower (fun _ => 1),
    reciprocalRadialWeight_continuous lower positive _ continuous_const⟩

theorem radialOrdinary_ae (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (field : RadialL2 dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialOrdinary dimension lower positive field radius =
        reciprocalRadialWeight lower (fun _ => 1) radius • field radius :=
  collarScalar_ae dimension lower _ field

theorem radialOrdinary_sqrt (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    radialOrdinary dimension lower positive (radialSqrtMap dimension lower field) = field := by
  apply Lp.ext
  filter_upwards [radialOrdinary_ae dimension lower positive (radialSqrtMap dimension lower field),
    radialSqrtMap_ae dimension lower field, ae_restrict_mem measurableSet_Icc]
    with radius decoded stored inside
  rw [decoded, stored, smul_smul, reciprocalRadialWeight, max_eq_right inside.1,
    one_div, inv_mul_cancel₀ (Real.sqrt_pos.2 (positive.trans_le inside.1)).ne', one_smul]

theorem radialPairing_ordinary (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (test : C(ℝ, ℝ)) (vector : ComplexEuclidean dimension) (field : RadialL2 dimension lower) :
    radialPairing lower positive test test.continuous vector field =
      collarPairing lower test vector (radialOrdinary dimension lower positive field) := by
  rw [radialPairing_general, collarPairing_integral]
  apply integral_congr_ae
  filter_upwards [radialOrdinary_ae dimension lower positive field] with radius literal
  rw [literal, inner_smul_right_eq_smul]

theorem diskRadial_ordinary_bulk (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : Grad.CircularHighWeak.diskGrade) :
    radialOrdinary 1 lower positive (diskL2Radial lower positive bounded mode (Grad.CircularHighWeak.diskBulk field)) =
      collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded (diskRadial lower positive bounded mode field)) := by
  have storage := (diskRadial_bulk lower positive bounded mode field).symm.trans
    (weightedRadialCoordinate_eq_sqrt 1 lower positive bounded 0 (diskRadial lower positive bounded mode field))
  exact (congrArg (radialOrdinary 1 lower positive) storage).trans
    (radialOrdinary_sqrt 1 lower positive _)

end Grad.CircularHighRegularity
