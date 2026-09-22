import ASG28CompactZeroPairing

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem compactPairing_separates (dimension : ℕ) (lower : ℝ)
    (field : CollarL2 (ComplexEuclidean dimension) lower)
    (vanishes : ∀ (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test),
      HasCompactSupport test → tsupport test ⊆ Ioo lower 1 →
        ∀ vector : ComplexEuclidean dimension, collarPairing lower ⟨test, smooth.continuous⟩ vector field = 0) : field = 0 := by
  have coordinateZero (coordinate : Fin dimension) :
      ∀ᵐ radius ∂volume.restrict (Icc lower 1), field radius coordinate = 0 := by
    let vector : ComplexEuclidean dimension := EuclideanSpace.single coordinate (1 : ℂ)
    let scalar : ℝ → ℂ := fun radius => inner ℂ vector (field radius)
    have locallyIntegrable : LocallyIntegrable scalar (volume.restrict (Icc lower 1)) :=
      ((innerSL ℂ vector).comp_memLp field).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
    have zeroOn : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 → scalar radius = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (locallyIntegrable.locallyIntegrableOn (Ioo lower 1))
      intro test smooth compact supported
      change (∫ radius in Icc lower 1, (⟨test, smooth.continuous⟩ : C(ℝ, ℝ)) radius • inner ℂ vector (field radius)) = 0
      rw [← collarPairing_integral lower ⟨test, smooth.continuous⟩ vector field]
      exact vanishes test smooth compact supported vector
    have inside : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [zeroOn, inside] with radius zeroAt insideAt
    simpa only [scalar, vector, EuclideanSpace.inner_single_left, map_one, one_mul] using zeroAt insideAt
  apply Lp.ext
  filter_upwards [ae_all_iff.2 coordinateZero, Lp.coeFn_zero (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))]
    with radius coordinates zeroRepresentative
  rw [zeroRepresentative]
  apply PiLp.ext
  intro coordinate
  exact coordinates coordinate

theorem collarTest_smul_integrable (dimension : ℕ) (lower : ℝ) (test : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    Integrable (fun radius => test radius • field radius) (volume.restrict (Icc lower 1)) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  obtain ⟨bound, bounded⟩ := (isCompact_Icc : IsCompact (Icc lower (1 : ℝ))).exists_bound_of_continuousOn test.continuous.continuousOn
  have major := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp field)).norm.const_mul bound
  apply major.mono' (test.continuous.aestronglyMeasurable.smul (Lp.memLp field).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  change ‖test radius • field radius‖ ≤ bound * ‖field radius‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (bounded radius inside) (norm_nonneg _)

theorem collarPairing_test_integral (dimension : ℕ) (lower : ℝ) (test : C(ℝ, ℝ))
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower test vector field = inner ℂ vector (∫ radius in Icc lower 1, test radius • field radius) := by
  rw [collarPairing_integral]
  calc
    _ = ∫ radius in Icc lower 1, inner ℂ vector (test radius • field radius) := by
      apply integral_congr_ae
      filter_upwards with radius
      exact (((innerSL ℂ vector).restrictScalars ℝ).map_smul (test radius) (field radius)).symm
    _ = _ := integral_inner (collarTest_smul_integrable dimension lower test field) vector

/-- AG2's zero-distributional-derivative conclusion from compact smooth
interior tests, with no boundary-test strengthening. -/
theorem compactWeakZero_eq_constant (dimension : ℕ) (lower : ℝ) (bounded : lower < 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CompactWeakDerivative dimension lower field 0) :
    ∃ value : ComplexEuclidean dimension, field = constantRadialL2 dimension lower value := by
  let bump : C(ℝ, ℝ) := ⟨normalizedInteriorTest lower bounded, (normalizedInteriorTest_smooth lower bounded).continuous⟩
  let value : ComplexEuclidean dimension := ∫ radius in Icc lower 1, bump radius • field radius
  refine ⟨value, sub_eq_zero.mp ?_⟩
  apply compactPairing_separates dimension lower
  intro test smooth compact supported vector
  rw [map_sub, compactWeakZero_pairing dimension lower bounded field weak test smooth compact supported,
    collarPairing_constant_field dimension lower bounded.le, collarPairing_test_integral]
  exact sub_self _

end Grad.AnnularSourceGraph
