import AJZ3SamePhysicalSourceRestriction
import AIY6ExactStrengthenedAngularSource
import AEI27ExactRhoPhysicalKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.AnnularStrongData Grad.AnnularCurrentSource
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy

abbrev originalBulkRestriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    DivisionRow dimension lower →L[ℂ] DivisionRow dimension upper :=
  collarBulkRestriction (ℤ × ℤ) dimension lower upper included

theorem originalBulkRestriction_ae (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      originalBulkRestriction dimension lower upper included field mode radius = field mode radius := by
  rw [ae_all_iff]
  intro mode
  exact collarL2Restriction_ae dimension lower upper included (field mode)

theorem originalBulkRestriction_lowRhoPhysical (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters upper positiveUpper
          (originalBulkRestriction dimension lower upper included field) radius mode =
        lowRhoPhysicalCoefficient parameters lower positiveLower field radius mode := by
  filter_upwards [originalBulkRestriction_ae dimension lower upper included field,
    ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  unfold lowRhoPhysicalCoefficient
  rw [actual]
  have same : lowRhoPhysicalWeight parameters upper positiveUpper radius mode =
      lowRhoPhysicalWeight parameters lower positiveLower radius mode := by
    change (max upper radius) ^ (-(7 / 4 : ℝ)) * Real.exp _ =
      (max lower radius) ^ (-(7 / 4 : ℝ)) * Real.exp _
    rw [max_eq_right inside.1, max_eq_right (included.trans inside.1)]
  rw [same]

theorem originalBulkRestriction_angularRecovery (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (angularRecoveryMap lower field) =
      angularRecoveryMap upper (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction 1 lower upper included (angularRecoverySymbol mode • field mode) =
    angularRecoverySymbol mode • collarL2Restriction 1 lower upper included (field mode)
  exact map_smul _ _ _

theorem originalBulkRestriction_strengthenedG (lower upper : ℝ) (included : lower ≤ upper)
    (g rg : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (strengthenedG lower g rg) =
      strengthenedG upper (originalBulkRestriction 1 lower upper included g)
        (originalBulkRestriction 1 lower upper included rg) := by
  unfold strengthenedG
  rw [map_add, originalBulkRestriction_angularRecovery]

theorem originalBulkRestriction_angularDecode (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (originalAngularDecode lower field) =
      originalAngularDecode upper (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction 1 lower upper included ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • field mode) =
    (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • collarL2Restriction 1 lower upper included (field mode)
  exact map_smul _ _ _

theorem originalBulkRestriction_angularBulk (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (sourceAngularBulk lower field) =
      sourceAngularBulk upper (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction 1 lower upper included (sourceAngularBulk lower field mode) = _
  rw [sourceAngularBulk_mode, sourceAngularBulk_mode]
  exact map_smul _ _ _

theorem originalBulkRestriction_angularRelation (lower upper : ℝ) (included : lower ≤ upper)
    (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode)
    (mode : ℤ × ℤ) :
    originalBulkRestriction 1 lower upper included rg mode =
      (Complex.I * (mode.1 : ℂ)) • originalBulkRestriction 1 lower upper included g mode := by
  change collarL2Restriction 1 lower upper included (rg mode) = _
  rw [relation, map_smul]
  rfl

theorem originalBulkRestriction_inserted (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (grade : ℕ) (field weighted : DivisionRow dimension lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • field mode)
    (mode : ℤ × ℤ) :
    originalBulkRestriction dimension lower upper included weighted mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        originalBulkRestriction dimension lower upper included field mode := by
  change collarL2Restriction dimension lower upper included (weighted mode) = _
  rw [same, map_smul]
  rfl

theorem sourceGraphRestriction_inserted (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell 0)
    (weighted : AnnularTotalSourceH1 parameters dimension lower angular cell grade)
    (same : ∀ mode : ℤ × ℤ, weighted mode = Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field mode)
    (mode : ℤ × ℤ) :
    sourceGraphRestriction parameters dimension lower upper included angular cell grade weighted mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade •
        sourceGraphRestriction parameters dimension lower upper included angular cell 0 field mode := by
  rw [sourceGraphRestriction_apply, same, map_smul, sourceGraphRestriction_apply]

end Grad.AnnularRestriction
