import ANR1Distribution

noncomputable section
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState
open Grad.NonlinearQuotientBounds (spatialPartial spatialPartial_smooth)

private def complexInnerReal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V →L[ℝ] V →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun first => (innerSL ℂ first).restrictScalars ℝ
      map_add' := by intro first second; ext value; exact inner_add_left _ _ _
      map_smul' := by
        intro scalar first
        ext value
        exact inner_smul_left_eq_smul first value scalar }
    1 (by
      intro first
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg first)
      intro second
      exact norm_inner_le_norm _ _)

private theorem bilinear_compact {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (pairing : V →L[ℝ] W →L[ℝ] Z) (first : SpatialPlane → V) (second : SpatialPlane → W)
    (compact : HasCompactSupport first) : HasCompactSupport (fun point => pairing (first point) (second point)) := by
  apply compact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro point nonzero
  change first point ≠ 0
  intro zero
  apply nonzero
  simp only [zero, map_zero, zero_apply]

private theorem integral_restrict_bilinear {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (pairing : V →L[ℝ] W →L[ℝ] Z) (first : SpatialPlane → V) (second : SpatialPlane → W)
    (supported : tsupport first ⊆ openUnitDisk) :
    (∫ point in openUnitDisk, pairing (first point) (second point)) =
      ∫ point, pairing (first point) (second point) := by
  have equality : (∫ point in openUnitDisk, pairing (first point) (second point)) =
      ∫ point in Set.univ, pairing (first point) (second point) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (Set.subset_univ _)
    intro point outside
    have zero : first point = 0 := image_eq_zero_of_notMem_tsupport
      (fun member => outside.2 (supported member))
    simp only [zero, map_zero, zero_apply]
  exact equality.trans (by rw [Measure.restrict_univ])

private theorem partial_support {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (direction : Fin 2) (field : SpatialPlane → V) :
    tsupport (spatialPartial direction field) ⊆ tsupport field := by
  apply Set.Subset.trans _ (tsupport_fderiv_subset ℝ)
  apply closure_mono
  intro point nonzero
  change fderiv ℝ field point ≠ 0
  intro zero
  apply nonzero
  change fderiv ℝ field point (spatialBasis direction) = 0
  rw [zero, zero_apply]

private theorem partial_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (direction : Fin 2) (field : SpatialPlane → V) (compact : HasCompactSupport field) :
    HasCompactSupport (spatialPartial direction field) :=
  compact.of_isClosed_subset (isClosed_tsupport _) (partial_support direction field)

/-- Literal compact Cartesian integration by parts for complex vector fields.
This does not require any boundary regularity of a completed unknown. -/
theorem compactGreen_first {dimension : ℕ} (direction : Fin 2)
    (test field : SpatialPlane → ComplexEuclidean dimension)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    (∫ point in openUnitDisk, inner ℂ (test point) (spatialPartial direction field point)) =
      -∫ point in openUnitDisk, inner ℂ (spatialPartial direction test point) (field point) := by
  let pairing : ComplexEuclidean dimension →L[ℝ] ComplexEuclidean dimension →L[ℝ] ℂ := complexInnerReal
  have derivativeSmooth := spatialPartial_smooth direction testSmooth
  have derivativeCompact := partial_compact direction test compact
  have derivativeSupported := (partial_support direction test).trans supported
  have integrableFirst : Integrable (fun point => pairing (spatialPartial direction test point) (field point)) :=
    ((pairing.continuous.comp derivativeSmooth.continuous).clm_apply fieldSmooth.continuous).integrable_of_hasCompactSupport
      (bilinear_compact pairing _ _ derivativeCompact)
  have integrableSecond : Integrable (fun point => pairing (test point) (spatialPartial direction field point)) :=
    ((pairing.continuous.comp testSmooth.continuous).clm_apply
      (spatialPartial_smooth direction fieldSmooth).continuous).integrable_of_hasCompactSupport
        (bilinear_compact pairing _ _ compact)
  have integrableProduct : Integrable (fun point => pairing (test point) (field point)) :=
    ((pairing.continuous.comp testSmooth.continuous).clm_apply fieldSmooth.continuous).integrable_of_hasCompactSupport
      (bilinear_compact pairing _ _ compact)
  have identity := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := pairing) (v := spatialBasis direction)
    integrableFirst integrableSecond integrableProduct
    (fun point _ => testSmooth.differentiable (by simp) point)
    (fun point _ => fieldSmooth.differentiable (by simp) point)
  exact (integral_restrict_bilinear pairing test (spatialPartial direction field) supported).trans
    (identity.trans (congrArg Neg.neg
      (integral_restrict_bilinear pairing (spatialPartial direction test) field derivativeSupported).symm))

theorem compactGreen_second {dimension : ℕ} (direction : Fin 2)
    (test field : SpatialPlane → ComplexEuclidean dimension)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    (∫ point in openUnitDisk,
      inner ℂ (spatialPartial direction test point) (spatialPartial direction field point)) =
      -∫ point in openUnitDisk,
        inner ℂ (spatialPartial direction (spatialPartial direction test) point) (field point) :=
  compactGreen_first direction (spatialPartial direction test) field
    (spatialPartial_smooth direction testSmooth) fieldSmooth (partial_compact direction test compact)
    ((partial_support direction test).trans supported)

end Grad.CircularHighRegularity
