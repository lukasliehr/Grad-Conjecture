import AJV3RestrictionScalarAndFourierMaps
import AJE1GenuineSourceGraphCharacters

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph

theorem collarL2Restriction_weightedCurveLinear (dimension : ℕ) (lower upper : ℝ)
    (included : lower ≤ upper) (curve : C(ℝ, ComplexEuclidean dimension)) :
    collarL2Restriction dimension lower upper included (weightedCurveLinear dimension lower curve) =
      weightedCurveLinear dimension upper curve := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae dimension lower upper included (weightedCurveLinear dimension lower curve),
    (radialToLp_ae lower curve curve.continuous).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    radialToLp_ae upper curve curve.continuous] with radius restriction source target
  change _ = radialToLp upper curve curve.continuous radius
  rw [restriction]
  exact source.trans target.symm

def sourceRadialAmbientRestrictionLinear (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    WeightedRadialAmbient dimension lower →ₗ[ℝ] WeightedRadialAmbient dimension upper where
  toFun field := WithLp.toLp 2 (fun slot : Fin 2 => collarL2Restriction dimension lower upper included (field slot))
  map_add' first second := by
    apply PiLp.ext
    intro slot
    exact map_add (collarL2Restriction dimension lower upper included) (first slot) (second slot)
  map_smul' scalar field := by
    apply PiLp.ext
    intro slot
    exact (collarL2Restriction dimension lower upper included).map_smul_of_tower scalar (field slot)

theorem sourceRadialAmbientRestrictionLinear_bound (dimension : ℕ) (lower upper : ℝ)
    (included : lower ≤ upper) (field : WeightedRadialAmbient dimension lower) :
    ‖sourceRadialAmbientRestrictionLinear dimension lower upper included field‖ ≤ ‖field‖ := by
  let output := sourceRadialAmbientRestrictionLinear dimension lower upper included field
  have first := collarL2Restriction_bound dimension lower upper included (field 0)
  have second := collarL2Restriction_bound dimension lower upper included (field 1)
  change ‖output 0‖ ≤ ‖field 0‖ at first
  change ‖output 1‖ ≤ ‖field 1‖ at second
  have firstSq := (sq_le_sq₀ (norm_nonneg (output 0)) (norm_nonneg (field 0))).mpr first
  have secondSq := (sq_le_sq₀ (norm_nonneg (output 1)) (norm_nonneg (field 1))).mpr second
  have inputNorm : ‖field‖ ^ 2 = ‖field 0‖ ^ 2 + ‖field 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have outputNorm : ‖output‖ ^ 2 = ‖output 0‖ ^ 2 + ‖output 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  change ‖output‖ ≤ ‖field‖
  nlinarith [norm_nonneg output, norm_nonneg field]

def sourceRadialAmbientRestriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    WeightedRadialAmbient dimension lower →L[ℝ] WeightedRadialAmbient dimension upper :=
  (sourceRadialAmbientRestrictionLinear dimension lower upper included).mkContinuous 1
    (fun field => by rw [one_mul]; exact sourceRadialAmbientRestrictionLinear_bound dimension lower upper included field)

theorem sourceRadialAmbientRestriction_core (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (core : SmoothRadialCore dimension) :
    sourceRadialAmbientRestriction dimension lower upper included (weightedRadialCore dimension lower core) =
      weightedRadialCore dimension upper core := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · exact collarL2Restriction_weightedCurveLinear dimension lower upper included core.val.val.1
  · exact collarL2Restriction_weightedCurveLinear dimension lower upper included core.val.val.2

theorem sourceRadialAmbientRestriction_mem (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WeightedRadialH1 dimension lower) :
    sourceRadialAmbientRestriction dimension lower upper included field.val ∈ WeightedRadialH1 dimension upper := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (((LinearMap.range (weightedRadialCore dimension upper)).isClosed_topologicalClosure).preimage
      ((sourceRadialAmbientRestriction dimension lower upper included).continuous.comp
        (WeightedRadialH1 dimension lower).subtypeL.continuous)) _ field
  intro core
  change sourceRadialAmbientRestriction dimension lower upper included (weightedRadialCore dimension lower core) ∈ _
  rw [sourceRadialAmbientRestriction_core]
  exact Submodule.le_topologicalClosure _ ⟨core, rfl⟩

/-- Both genuine weighted value and derivative are restricted. Membership is
in the closure of the same global smooth radial cores. -/
def sourceRadialRestriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    WeightedRadialH1 dimension lower →L[ℝ] WeightedRadialH1 dimension upper :=
  ((sourceRadialAmbientRestriction dimension lower upper included).comp
    (WeightedRadialH1 dimension lower).subtypeL).codRestrict (WeightedRadialH1 dimension upper)
    (sourceRadialAmbientRestriction_mem dimension lower upper included)

theorem sourceRadialRestriction_coordinate (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WeightedRadialH1 dimension lower) (slot : Fin 2) :
    weightedRadialCoordinate dimension upper slot (sourceRadialRestriction dimension lower upper included field) =
      collarL2Restriction dimension lower upper included (weightedRadialCoordinate dimension lower slot field) := rfl

theorem sourceRadialRestriction_bound (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WeightedRadialH1 dimension lower) :
    ‖sourceRadialRestriction dimension lower upper included field‖ ≤ ‖field‖ :=
  sourceRadialAmbientRestrictionLinear_bound dimension lower upper included field.val

theorem sourceRadialRestriction_core (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (core : SmoothRadialCore dimension) :
    sourceRadialRestriction dimension lower upper included (weightedRadialCoreInto dimension lower core) =
      weightedRadialCoreInto dimension upper core := by
  apply Subtype.ext
  exact sourceRadialAmbientRestriction_core dimension lower upper included core

theorem sourceRadialRestriction_id (dimension : ℕ) (lower : ℝ) (field : WeightedRadialH1 dimension lower) :
    sourceRadialRestriction dimension lower lower le_rfl field = field := by
  apply Subtype.ext
  apply PiLp.ext
  intro slot
  exact collarL2Restriction_id dimension lower (field.val slot)

theorem sourceRadialRestriction_comp (dimension : ℕ) (lower middle upper : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper) (field : WeightedRadialH1 dimension lower) :
    sourceRadialRestriction dimension middle upper second (sourceRadialRestriction dimension lower middle first field) =
      sourceRadialRestriction dimension lower upper (first.trans second) field := by
  apply Subtype.ext
  apply PiLp.ext
  intro slot
  exact collarL2Restriction_comp dimension lower middle upper first second (field.val slot)

end Grad.AnnularRestriction
