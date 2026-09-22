import AJW1HighRestrictionAmbient
import AJV1ActualCollarL2Restriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Restriction reuses the same global smooth value/slope functions, with literal sqrt(r) storage. -/
theorem collarL2Restriction_weightedCurve (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (first second : C(ℝ, ComplexEuclidean dimension)) (same : EqOn first second (Icc upper 1)) :
    collarL2Restriction dimension lower upper included (weightedCurveComplex dimension lower first) =
      weightedCurveComplex dimension upper second := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae dimension lower upper included (weightedCurveComplex dimension lower first),
    (radialToLp_ae lower first first.continuous).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    radialToLp_ae upper second second.continuous, ae_restrict_mem measurableSet_Icc]
    with radius restriction source target inside
  rw [restriction]
  change radialToLp lower first first.continuous radius = radialToLp upper second second.continuous radius
  rw [source, target, same inside]

theorem annularPotentialWeight_restrict (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper) (mode cell : ℤ) :
    EqOn (annularPotentialWeight lower length lowerPositive mode cell)
      (annularPotentialWeight upper length upperPositive mode cell) (Icc upper 1) := by
  intro radius inside
  change Real.sqrt (annularPotential length (max lower radius) mode cell) =
    Real.sqrt (annularPotential length (max upper radius) mode cell)
  rw [max_eq_right (included.trans inside.1), max_eq_right inside.1]

def highEnergyAmbientRestriction (lower upper : ℝ) (included : lower ≤ upper) :
    AnnularEnergyAmbient lower →L[ℂ] AnnularEnergyAmbient upper :=
  highAmbientRadialMap lower upper (collarL2Restriction 1 lower upper included)
    (collarL2Restriction_bound 1 lower upper included)

theorem highEnergyAmbientRestriction_norm_le (lower upper : ℝ) (included : lower ≤ upper)
    (field : AnnularEnergyAmbient lower) :
    ‖highEnergyAmbientRestriction lower upper included field‖ ≤ ‖field‖ :=
  highAmbientRadialMap_norm_le lower upper (collarL2Restriction 1 lower upper included)
    (collarL2Restriction_bound 1 lower upper included) field

/-- The derivative, potential and true outer scalar coordinates are those
of the SAME smooth function on the smaller collar. -/
theorem highModeRadialMap_energyCore (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper) (mode cell : ℤ)
    (core : complexSmoothRadialCore 1) :
    highModeRadialMap lower upper (collarL2Restriction 1 lower upper included)
      (annularModeEnergyCore lower length lowerPositive mode cell core) =
    annularModeEnergyCore upper length upperPositive mode cell core := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact collarL2Restriction_weightedCurve 1 lower upper included core.val.2 core.val.2 (fun _ _ => rfl)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    apply Prod.ext
    · apply collarL2Restriction_weightedCurve 1 lower upper included
      intro radius inside
      change annularPotentialWeight lower length lowerPositive mode cell radius • core.val.1 radius =
        annularPotentialWeight upper length upperPositive mode cell radius • core.val.1 radius
      rw [annularPotentialWeight_restrict lower upper length lowerPositive upperPositive included mode cell inside]
    · rfl

/-- Restriction preserves the actual finite smooth core before completion. -/
theorem highEnergyAmbientRestriction_core (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyAmbientRestriction lower upper included (finiteAnnularEnergyCore lower length lowerPositive core) =
      finiteAnnularEnergyCore upper length upperPositive core := by
  apply lp.ext
  funext mode
  rw [finiteAnnularEnergyCore_apply]
  change highModeRadialMap lower upper (collarL2Restriction 1 lower upper included)
    (finiteAnnularEnergyCore lower length lowerPositive core mode) = _
  rw [finiteAnnularEnergyCore_apply]
  exact highModeRadialMap_energyCore lower upper length lowerPositive upperPositive included mode.val.1 mode.val.2 (core mode)

theorem highEnergyAmbientRestriction_mem (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper)
    (field : annularEnergySpace lower length lowerPositive) :
    highEnergyAmbientRestriction lower upper included field.val ∈ annularEnergySpace upper length upperPositive := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length lowerPositive)
    ((LinearMap.range (finiteAnnularEnergyCore upper length upperPositive)).isClosed_topologicalClosure.preimage
      ((highEnergyAmbientRestriction lower upper included).continuous.comp continuous_subtype_val)) _ field
  intro core
  change highEnergyAmbientRestriction lower upper included (finiteAnnularEnergyCore lower length lowerPositive core) ∈ _
  rw [highEnergyAmbientRestriction_core]
  exact (annularEnergyCoreInto upper length upperPositive core).property

/-- Actual closed high energy restriction, proved from its defining smooth core. -/
def highEnergyRestriction (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper) :
    annularEnergySpace lower length lowerPositive →L[ℂ] annularEnergySpace upper length upperPositive :=
  ((highEnergyAmbientRestriction lower upper included).comp (annularEnergySpace lower length lowerPositive).subtypeL).codRestrict _
    (highEnergyAmbientRestriction_mem lower upper length lowerPositive upperPositive included)

theorem highEnergyRestriction_bound (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper)
    (field : annularEnergySpace lower length lowerPositive) :
    ‖highEnergyRestriction lower upper length lowerPositive upperPositive included field‖ ≤ ‖field‖ :=
  highEnergyAmbientRestriction_norm_le lower upper included field.val

end Grad.AnnularRestriction
