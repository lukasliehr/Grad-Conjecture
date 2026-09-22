import AKAP1SameValueBoundedH1Lift
import DR1Jet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 2000

open MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets
open Grad.WeightedJets.Restriction Grad.WeightedJets.ZeroExtension

/-- Restrict the SAME volume representative to the disk. -/
def startupPlaneRestrictionFor (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) : FieldL2 →L[ℂ] StartupL2 3 :=
  (fieldRestriction CellValues (Set.subset_univ openUnitDisk)).comp
    equivalence.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Zero extension of an L2 field carries no boundary regularity assertion. -/
def startupPlaneExtensionFor (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) : StartupL2 3 →L[ℂ] FieldL2 :=
  equivalence.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fieldExtension CellValues openUnitDisk openUnitDisk_isOpen.measurableSet).toContinuousLinearMap

theorem startupPlaneRestrictionFor_apply (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) (field : FieldL2) :
    startupPlaneRestrictionFor equivalence field = fieldRestriction CellValues (Set.subset_univ openUnitDisk)
      (equivalence.symm field) := rfl

theorem startupPlaneExtensionFor_apply (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) (field : StartupL2 3) :
    startupPlaneExtensionFor equivalence field = equivalence
      (fieldExtension CellValues openUnitDisk openUnitDisk_isOpen.measurableSet field) := rfl

theorem startupPlaneRestrictionFor_norm_le (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) (field : FieldL2) :
    ‖startupPlaneRestrictionFor equivalence field‖ ≤ ‖field‖ := by
  exact (fieldRestriction_norm_le CellValues (Set.subset_univ openUnitDisk) _).trans_eq
    (equivalence.symm.norm_map field)

theorem startupPlaneExtensionFor_norm (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) (field : StartupL2 3) :
    ‖startupPlaneExtensionFor equivalence field‖ = ‖field‖ :=
  (equivalence.norm_map _).trans
    (fieldExtension_norm CellValues openUnitDisk openUnitDisk_isOpen.measurableSet field)

theorem startupPlaneRestrictionFor_opNorm (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) : ‖startupPlaneRestrictionFor equivalence‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using startupPlaneRestrictionFor_norm_le equivalence field

theorem startupPlaneExtensionFor_opNorm (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2) : ‖startupPlaneExtensionFor equivalence‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  exact (startupPlaneExtensionFor_norm equivalence field).le.trans_eq (one_mul _).symm

abbrev startupPlaneRestriction : FieldL2 →L[ℂ] StartupL2 3 :=
  startupPlaneRestrictionFor startupWholePlaneField

abbrev startupPlaneExtension : StartupL2 3 →L[ℂ] FieldL2 :=
  startupPlaneExtensionFor startupWholePlaneField

theorem startupPlaneRestriction_norm_le (field : FieldL2) :
    ‖startupPlaneRestriction field‖ ≤ ‖field‖ :=
  startupPlaneRestrictionFor_norm_le startupWholePlaneField field

theorem startupPlaneExtension_norm (field : StartupL2 3) :
    ‖startupPlaneExtension field‖ = ‖field‖ :=
  startupPlaneExtensionFor_norm startupWholePlaneField field

theorem startupPlaneRestriction_opNorm : ‖startupPlaneRestriction‖ ≤ 1 :=
  startupPlaneRestrictionFor_opNorm startupWholePlaneField

theorem startupPlaneExtension_opNorm : ‖startupPlaneExtension‖ ≤ 1 :=
  startupPlaneExtensionFor_opNorm startupWholePlaneField

theorem startupH1_diskGraph_for
    (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2)
    (field : FieldH1)
    (realized : ∃ graph : GraphGrade 3 1 0 Set.univ,
      equivalence (base 3 1 Set.univ (fun _ => 0) graph) = valueInclusion field ∧ ‖graph‖ = ‖field‖) :
    ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = startupPlaneRestrictionFor equivalence (valueInclusion field) ∧
      ‖graph‖ ≤ ‖field‖ := by
  obtain ⟨whole, represented, sameNorm⟩ := realized
  refine ⟨restriction 3 1 (Set.subset_univ openUnitDisk) MeasurableSet.univ (fun _ => 0) whole, ?_,
    (restriction_norm_le 3 1 (Set.subset_univ openUnitDisk) MeasurableSet.univ (fun _ => 0) whole).trans_eq sameNorm⟩
  rw [restriction_base]
  rw [startupPlaneRestrictionFor_apply]
  apply congrArg
  exact equivalence.injective (represented.trans (equivalence.apply_symm_apply (valueInclusion field)).symm)

/-- Every actual H1 input yields its SAME disk first graph with no loss. -/
theorem startupH1_diskGraph_exists (field : FieldH1) :
    ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = startupPlaneRestriction (valueInclusion field) ∧
      ‖graph‖ ≤ ‖field‖ :=
  startupH1_diskGraph_for startupWholePlaneField field (startupH1_firstGraph_exists field)

end Grad.CartesianStartup
