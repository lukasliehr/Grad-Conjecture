import ASG33CompletedContinuousSection

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def radialClamp (lower : ℝ) (bounded : lower ≤ 1) (radius : ℝ) : Icc lower (1 : ℝ) :=
  ⟨max lower (min 1 radius), le_max_left _ _, max_le bounded (min_le_left _ _)⟩

theorem radialClamp_continuous (lower : ℝ) (bounded : lower ≤ 1) : Continuous (radialClamp lower bounded) := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

theorem radialClamp_eq (lower : ℝ) (bounded : lower ≤ 1) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    radialClamp lower bounded radius = ⟨radius, inside⟩ := by
  apply Subtype.ext
  simp only [radialClamp, min_eq_right inside.2, max_eq_right inside.1]

def radialSectionExtension (dimension : ℕ) (lower : ℝ) (bounded : lower ≤ 1)
    (sectionValue : RadialContinuousSection dimension lower) : C(ℝ, ComplexEuclidean dimension) :=
  ⟨fun radius => sectionValue (radialClamp lower bounded radius),
    sectionValue.continuous.comp (radialClamp_continuous lower bounded)⟩

def radialSectionL2Linear (dimension : ℕ) (lower : ℝ) (bounded : lower ≤ 1) :
    RadialContinuousSection dimension lower →ₗ[ℝ] CollarL2 (ComplexEuclidean dimension) lower where
  toFun sectionValue := collarContinuousL2 (ComplexEuclidean dimension) lower
    (radialSectionExtension dimension lower bounded sectionValue)
  map_add' first second := by
    have additive : radialSectionExtension dimension lower bounded (first + second) =
        radialSectionExtension dimension lower bounded first + radialSectionExtension dimension lower bounded second := by
      apply ContinuousMap.ext
      intro radius
      rfl
    rw [additive, map_add]
  map_smul' scalar sectionValue := by
    have scaled : radialSectionExtension dimension lower bounded (scalar • sectionValue) =
        scalar • radialSectionExtension dimension lower bounded sectionValue := by
      apply ContinuousMap.ext
      intro radius
      rfl
    rw [scaled, map_smul]
    rfl

theorem radialSectionL2Linear_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (sectionValue : RadialContinuousSection dimension lower) :
    ‖radialSectionL2Linear dimension lower bounded sectionValue‖ ≤ 1 * ‖sectionValue‖ := by
  have normSq := collarContinuousL2_norm_sq (ComplexEuclidean dimension) lower bounded
    (radialSectionExtension dimension lower bounded sectionValue)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) bounded
    (((radialSectionExtension dimension lower bounded sectionValue).continuous.norm.pow 2).intervalIntegrable lower 1)
    (continuous_const.intervalIntegrable lower 1)
    (fun radius _ => pow_le_pow_left₀ (norm_nonneg _) (sectionValue.norm_coe_le_norm (radialClamp lower bounded radius)) 2)
  rw [intervalIntegral.integral_const] at comparison
  change (∫ radius in lower..1, ‖radialSectionExtension dimension lower bounded sectionValue radius‖ ^ 2) ≤
    (1 - lower) * ‖sectionValue‖ ^ 2 at comparison
  have shortened : (1 - lower) * ‖sectionValue‖ ^ 2 ≤ ‖sectionValue‖ ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) (by linarith)
  change ‖collarContinuousL2 (ComplexEuclidean dimension) lower
    (radialSectionExtension dimension lower bounded sectionValue)‖ ≤ 1 * ‖sectionValue‖
  nlinarith [norm_nonneg (collarContinuousL2 (ComplexEuclidean dimension) lower
    (radialSectionExtension dimension lower bounded sectionValue)), norm_nonneg sectionValue]

def radialSectionL2 (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    RadialContinuousSection dimension lower →L[ℝ] CollarL2 (ComplexEuclidean dimension) lower :=
  (radialSectionL2Linear dimension lower bounded).mkContinuous 1
    (radialSectionL2Linear_bound dimension lower positive bounded)

theorem radialSectionL2_core (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : SmoothRadialCore dimension) :
    radialSectionL2 dimension lower positive bounded (smoothRadialSection dimension lower core) =
      smoothRadialValueL2 dimension lower core := by
  apply Lp.ext
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (collarContinuous_memLp (ComplexEuclidean dimension) lower
      (radialSectionExtension dimension lower bounded (smoothRadialSection dimension lower core))).coeFn_toLp,
    (collarContinuous_memLp (ComplexEuclidean dimension) lower core.val.val.1).coeFn_toLp]
    with radius inside sectionLaw coreLaw
  change collarContinuousL2 (ComplexEuclidean dimension) lower
      (radialSectionExtension dimension lower bounded (smoothRadialSection dimension lower core)) radius = _ at sectionLaw
  change collarContinuousL2 (ComplexEuclidean dimension) lower core.val.val.1 radius = _ at coreLaw
  change collarContinuousL2 (ComplexEuclidean dimension) lower
      (radialSectionExtension dimension lower bounded (smoothRadialSection dimension lower core)) radius =
    collarContinuousL2 (ComplexEuclidean dimension) lower core.val.val.1 radius
  rw [sectionLaw, coreLaw]
  change core.val.val.1 (radialClamp lower bounded radius).val = core.val.val.1 radius
  rw [radialClamp_eq lower bounded radius inside]

theorem weightedRadialSection_bulk (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower) :
    radialSectionL2 dimension lower positive bounded.le (weightedRadialSection dimension lower positive bounded field) =
      collarH1Coordinate (ComplexEuclidean dimension) lower 0
        (weightedToOrdinary dimension lower positive bounded.le field) := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq ((radialSectionL2 dimension lower positive bounded.le).continuous.comp
      (weightedRadialSection dimension lower positive bounded).continuous)
      ((collarH1Coordinate (ComplexEuclidean dimension) lower 0).continuous.comp
        (weightedToOrdinary dimension lower positive bounded.le).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [weightedRadialSection_core, radialSectionL2_core, weightedToOrdinary_core, collarH1Coordinate_core_zero]
  rfl

end Grad.AnnularSourceGraph
