import AKCX39SameCutoffAllSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered

/-- Derivatives of a supported weak graph retain the SAME closed support.
Restriction to the open complement has zero base, hence is the zero graph. -/
theorem startupRecoveredDerivative_supported {dimension order weight : ℕ} {support : Set Spatial}
    (closed : IsClosed support) (field : GraphGrade dimension order weight openUnitDisk)
    (supported : SupportedField (CellValues dimension) openUnitDisk support
      (base dimension order openUnitDisk (fun _ => weight) field)) (index : JetIndex order) :
    SupportedField (CellValues dimension) openUnitDisk support
      (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index field) := by
  let outside := supportᶜ ∩ openUnitDisk
  have openOutside : IsOpen outside := closed.isOpen_compl.inter openUnitDisk_isOpen
  have included : outside ⊆ openUnitDisk := inter_subset_right
  let restricted := Restriction.restriction dimension order included openUnitDisk_isOpen.measurableSet (fun _ => weight) field
  have restrictedZero : restricted = 0 := by
    apply base_injective dimension order outside openOutside (fun _ => weight)
    rw [map_zero]
    change base dimension order outside (fun _ => weight)
      (Restriction.restriction dimension order included openUnitDisk_isOpen.measurableSet (fun _ => weight) field) = 0
    rw [Restriction.restriction_base]
    apply Lp.ext
    filter_upwards [Restriction.fieldRestriction_ae (CellValues dimension) included
        (base dimension order openUnitDisk (fun _ => weight) field),
      ae_restrict_of_ae_restrict_of_subset included supported,
      ae_restrict_mem openOutside.measurableSet,
      Lp.coeFn_zero (CellValues dimension) 2 (volume.restrict outside)] with point same zero inside zeroValue
    rw [same,zero inside.1,zeroValue]
    rfl
  have derivativeZero : Restriction.fieldRestriction (CellValues dimension) included
      (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index field) = 0 := by
    rw [← Restriction.restriction_recoveredDerivative dimension order included openUnitDisk_isOpen.measurableSet (fun _ => weight) index field]
    change Realization.recoveredDerivative dimension order outside (fun _ => weight) index restricted = 0
    rw [restrictedZero,map_zero]
  have zeroOutside : ∀ᵐ point ∂volume.restrict outside,
      Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index field point = 0 := by
    filter_upwards [Restriction.fieldRestriction_ae (CellValues dimension) included
      (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index field),
      Lp.coeFn_zero (CellValues dimension) 2 (volume.restrict outside)] with point same zeroValue
    rw [derivativeZero] at same
    exact same.symm.trans zeroValue
  apply (ae_restrict_iff' closed.measurableSet.compl).mp
  rw [Measure.restrict_restrict closed.measurableSet.compl]
  exact zeroOutside

theorem startupOrderedDerivative_supported {dimension order rank weight : ℕ} {support : Set Spatial}
    (closed : IsClosed support) (field : GraphGrade dimension order weight openUnitDisk)
    (supported : SupportedField (CellValues dimension) openUnitDisk support
      (base dimension order openUnitDisk (fun _ => weight) field))
    (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    SupportedField (CellValues dimension) openUnitDisk support
      (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound field word) :=
  startupRecoveredDerivative_supported closed field supported (wordIndex bound word)

end Grad.CartesianStartup
