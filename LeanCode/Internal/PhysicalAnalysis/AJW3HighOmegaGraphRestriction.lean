import AJW2HighEnergyCoreRestriction
import AJV3RestrictionScalarAndFourierMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.AnnularOmegaGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarL2Restriction_radialOrdinary (lower upper : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper) (field : RadialL2 1 lower) :
    collarL2Restriction 1 lower upper included (radialOrdinary 1 lower lowerPositive field) =
      radialOrdinary 1 upper upperPositive (collarL2Restriction 1 lower upper included field) := by
  apply collarL2Restriction_scalar 1 lower upper included
  intro radius inside
  change 1 / Real.sqrt (max lower radius) = 1 / Real.sqrt (max upper radius)
  rw [max_eq_right (included.trans inside.1), max_eq_right inside.1]

theorem annularOmegaCurve_restrict (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper) (mode : HighAnnularMode) :
    EqOn (annularOmegaCurve lower length lowerPositive mode)
      (annularOmegaCurve upper length upperPositive mode) (Icc upper 1) := by
  intro radius inside
  change annularOmega length (max lower radius) mode = annularOmega length (max upper radius) mode
  rw [max_eq_right (included.trans inside.1), max_eq_right inside.1]

/-- Both literal omega-normalized value/slope coordinates restrict without a new multiplier. -/
def highOmegaAmbientRestriction (lower upper : ℝ) (included : lower ≤ upper) :
    AnnularOmegaAmbient lower →L[ℂ] AnnularOmegaAmbient upper :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk upper)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun coordinate => (collarBulkRestriction HighAnnularMode 1 lower upper included).comp
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => AnnularBulk lower) coordinate)))

theorem highOmegaAmbientRestriction_apply (lower upper : ℝ) (included : lower ≤ upper)
    (field : AnnularOmegaAmbient lower) (coordinate : Fin 2) (mode : HighAnnularMode) :
    highOmegaAmbientRestriction lower upper included field coordinate mode =
      collarL2Restriction 1 lower upper included (field coordinate mode) := rfl

theorem highOmegaAmbientRestriction_bound (lower upper : ℝ) (included : lower ≤ upper)
    (field : AnnularOmegaAmbient lower) : ‖highOmegaAmbientRestriction lower upper included field‖ ≤ ‖field‖ := by
  have input : ‖field‖ ^ 2 = ‖field 0‖ ^ 2 + ‖field 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have output : ‖highOmegaAmbientRestriction lower upper included field‖ ^ 2 =
      ‖highOmegaAmbientRestriction lower upper included field 0‖ ^ 2 +
      ‖highOmegaAmbientRestriction lower upper included field 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have value := collarBulkRestriction_bound HighAnnularMode 1 lower upper included (field 0)
  have slope := collarBulkRestriction_bound HighAnnularMode 1 lower upper included (field 1)
  change ‖highOmegaAmbientRestriction lower upper included field‖ ^ 2 =
    ‖collarBulkRestriction HighAnnularMode 1 lower upper included (field 0)‖ ^ 2 +
    ‖collarBulkRestriction HighAnnularMode 1 lower upper included (field 1)‖ ^ 2 at output
  exact restrictionPairNorm_mono _ _ _ _ _ _
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    input output value slope

/-- Membership follows from the genuine weak derivative and radius locality
of omega on the smaller collar. -/
theorem highOmegaAmbientRestriction_mem (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    highOmegaAmbientRestriction lower upper included field.val ∈
      annularOmegaGraph upper length upperPositive lengthPositive := by
  rw [annularOmegaGraph_mem_iff]
  intro mode
  have source := (annularOmegaGraph_mem_iff lower length lowerPositive lengthPositive field.val).mp field.property mode
  have restricted := collarWeakDerivative_restrict 1 lower upper included upperPositive upperBounded _ _ source
  rw [collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included,
    collarL2Restriction_scalar 1 lower upper included _ _
      (annularOmegaCurve_restrict lower upper length lowerPositive upperPositive included mode),
    collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included] at restricted
  exact restricted

def highOmegaRestriction (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) :
    annularOmegaGraph lower length lowerPositive lengthPositive →L[ℂ]
      annularOmegaGraph upper length upperPositive lengthPositive :=
  ((highOmegaAmbientRestriction lower upper included).comp
    (annularOmegaGraph lower length lowerPositive lengthPositive).subtypeL).codRestrict _
    (highOmegaAmbientRestriction_mem lower upper length lowerPositive upperPositive upperBounded lengthPositive included)

theorem highOmegaRestriction_bound (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    ‖highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field‖ ≤ ‖field‖ :=
  highOmegaAmbientRestriction_bound lower upper included field.val

end Grad.AnnularRestriction
