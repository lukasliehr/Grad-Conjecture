import DR1Field
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (DomainL2 CellValues PhysicalValue)
open scoped ContDiff

namespace Grad.WeightedJets.ZeroExtension

variable (Value : Type*) [NormedAddCommGroup Value]
variable (domain : Set Spatial) (measurable : MeasurableSet domain)

def extendValue (field : DomainL2 Value domain) : DomainL2 Value Set.univ :=
  (show MemLp (domain.indicator field) 2 (volume.restrict Set.univ) from by
    rw [Measure.restrict_univ]
    exact (memLp_indicator_iff_restrict measurable).mpr (Lp.memLp field)).toLp
      (domain.indicator field)

theorem extendValue_ae_restrict (field : DomainL2 Value domain) :
    extendValue Value domain measurable field =ᵐ[volume.restrict Set.univ] domain.indicator field :=
  MemLp.coeFn_toLp _

theorem extendValue_ae (field : DomainL2 Value domain) :
    extendValue Value domain measurable field =ᵐ[volume] domain.indicator field :=
  (extendValue_ae_restrict Value domain measurable field).filter_mono (by simp)

theorem extendValue_norm (field : DomainL2 Value domain) :
    ‖extendValue Value domain measurable field‖ = ‖field‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (extendValue_ae_restrict Value domain measurable field),
    Measure.restrict_univ,
    eLpNorm_indicator_eq_eLpNorm_restrict measurable]

theorem extendValue_add (first second : DomainL2 Value domain) :
    extendValue Value domain measurable (first + second) =
      extendValue Value domain measurable first + extendValue Value domain measurable second := by
  apply Lp.ext
  apply ae_restrict_of_ae
  have original : ∀ᵐ point ∂volume, point ∈ domain →
      (first + second) point = first point + second point :=
    (ae_restrict_iff' measurable).mp (Lp.coeFn_add first second)
  have target := (Lp.coeFn_add (extendValue Value domain measurable first)
    (extendValue Value domain measurable second)).filter_mono
      (show ae volume ≤ ae (volume.restrict Set.univ) by simp)
  filter_upwards [extendValue_ae Value domain measurable (first + second),
    extendValue_ae Value domain measurable first, extendValue_ae Value domain measurable second,
    original, target] with point totalAt firstAt secondAt originalAt targetAt
  rw [totalAt, targetAt, Pi.add_apply, firstAt, secondAt]
  by_cases inside : point ∈ domain
  · simpa only [Set.indicator_of_mem inside] using originalAt inside
  · simp only [Set.indicator_of_notMem inside, add_zero]

variable [InnerProductSpace ℂ Value]

theorem extendValue_smul (scalar : ℂ) (field : DomainL2 Value domain) :
    extendValue Value domain measurable (scalar • field) =
      scalar • extendValue Value domain measurable field := by
  apply Lp.ext
  apply ae_restrict_of_ae
  have original : ∀ᵐ point ∂volume, point ∈ domain →
      (scalar • field) point = scalar • field point :=
    (ae_restrict_iff' measurable).mp (Lp.coeFn_smul scalar field)
  have target := (Lp.coeFn_smul scalar (extendValue Value domain measurable field)).filter_mono
    (show ae volume ≤ ae (volume.restrict Set.univ) by simp)
  filter_upwards [extendValue_ae Value domain measurable (scalar • field),
    extendValue_ae Value domain measurable field, original, target]
    with point scaledAt fieldAt originalAt targetAt
  rw [scaledAt, targetAt, Pi.smul_apply, fieldAt]
  by_cases inside : point ∈ domain
  · simpa only [Set.indicator_of_mem inside] using originalAt inside
  · simp only [Set.indicator_of_notMem inside, smul_zero]

def fieldExtension : DomainL2 Value domain →ₗᵢ[ℂ] DomainL2 Value Set.univ where
  toFun := extendValue Value domain measurable
  map_add' := extendValue_add Value domain measurable
  map_smul' := extendValue_smul Value domain measurable
  norm_map' := extendValue_norm Value domain measurable

theorem fieldExtension_ae (field : DomainL2 Value domain) :
    fieldExtension Value domain measurable field =ᵐ[volume] domain.indicator field :=
  extendValue_ae Value domain measurable field

theorem fieldExtension_inside (field : DomainL2 Value domain) :
    fieldExtension Value domain measurable field =ᵐ[volume.restrict domain] field := by
  filter_upwards [ae_restrict_of_ae (fieldExtension_ae Value domain measurable field),
    ae_restrict_mem measurable] with point represented inside
  rw [represented, Set.indicator_of_mem inside]

theorem fieldExtension_outside (field : DomainL2 Value domain) :
    fieldExtension Value domain measurable field =ᵐ[volume.restrict domainᶜ] 0 := by
  filter_upwards [ae_restrict_of_ae (fieldExtension_ae Value domain measurable field),
    ae_restrict_mem measurable.compl] with point represented outside
  simp only [represented, Set.indicator_of_notMem outside, Pi.zero_apply]

theorem fieldExtension_norm (field : DomainL2 Value domain) :
    ‖fieldExtension Value domain measurable field‖ = ‖field‖ :=
  (fieldExtension Value domain measurable).norm_map field

theorem fieldExtension_injective : Function.Injective (fieldExtension Value domain measurable) :=
  (fieldExtension Value domain measurable).injective

theorem restriction_extension (field : DomainL2 Value domain) :
    Restriction.fieldRestriction Value (Set.subset_univ domain)
      (fieldExtension Value domain measurable field) = field := by
  apply Lp.ext
  exact (Restriction.fieldRestriction_ae Value (Set.subset_univ domain)
    (fieldExtension Value domain measurable field)).trans (fieldExtension_inside Value domain measurable field)

theorem fieldExtension_naturality {Target : Type*} [NormedAddCommGroup Target]
    [InnerProductSpace ℂ Target] (mapping : Value →L[ℂ] Target) (field : DomainL2 Value domain) :
    fieldExtension Target domain measurable ((mapping.compLpL 2 (volume.restrict domain)) field) =
      mapping.compLpL 2 (volume.restrict Set.univ) (fieldExtension Value domain measurable field) := by
  apply Lp.ext
  apply ae_restrict_of_ae
  have original : ∀ᵐ point ∂volume, point ∈ domain →
      (mapping.compLpL 2 (volume.restrict domain) field) point = mapping (field point) :=
    (ae_restrict_iff' measurable).mp (mapping.coeFn_compLpL field)
  have target := (mapping.coeFn_compLpL (fieldExtension Value domain measurable field)).filter_mono
    (show ae volume ≤ ae (volume.restrict Set.univ) by simp)
  filter_upwards [fieldExtension_ae Target domain measurable
      (mapping.compLpL 2 (volume.restrict domain) field),
    fieldExtension_ae Value domain measurable field, original, target]
    with point mappedAt fieldAt originalAt targetAt
  rw [mappedAt, targetAt, fieldAt]
  by_cases inside : point ∈ domain
  · simpa only [Set.indicator_of_mem inside] using originalAt inside
  · simp only [Set.indicator_of_notMem inside, map_zero]

end Grad.WeightedJets.ZeroExtension
