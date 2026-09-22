import AKAY19ScaledWeakConjugation
import DIL1Tests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.SpatialDilation

theorem startupDilation_inclusion (scale : Scale) : openUnitDisk ⊆ pullDomain scale openUnitDisk := by
  intro point inside
  change ‖scale.val • point‖ < 1
  rw [norm_smul, Real.norm_of_nonneg scale.property.1.le]
  exact (mul_le_of_le_one_left (norm_nonneg point) scale.property.2).trans_lt inside

/-- The existing exact inward dilation followed by existing restriction. -/
def startupDilation (scale : Scale) (field : StartupL2 3) : StartupL2 3 :=
  Restriction.fieldRestriction (Grad.GenericCarriers.CellValues 3) (startupDilation_inclusion scale)
    (rawValue 3 openUnitDisk openUnitDisk_isOpen.measurableSet scale field)

theorem startupDilation_norm (scale : Scale) (field : StartupL2 3) :
    ‖startupDilation scale field‖ ≤ scale.val⁻¹ * ‖field‖ :=
  (Restriction.fieldRestriction_norm_le (Grad.GenericCarriers.CellValues 3) (startupDilation_inclusion scale)
    (rawValue 3 openUnitDisk openUnitDisk_isOpen.measurableSet scale field)).trans_eq
      (rawValue_norm 3 openUnitDisk openUnitDisk_isOpen.measurableSet scale field)

theorem startupDilation_ae (scale : Scale) (field : StartupL2 3) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, startupDilation scale field point = field (scale.val • point) := by
  exact (Restriction.fieldRestriction_ae (Grad.GenericCarriers.CellValues 3) (startupDilation_inclusion scale)
    (rawValue 3 openUnitDisk openUnitDisk_isOpen.measurableSet scale field)).trans
    (ae_restrict_of_ae_restrict_of_subset (startupDilation_inclusion scale)
      (rawValue_ae 3 openUnitDisk openUnitDisk_isOpen.measurableSet scale field))

theorem startupDilation_pull_ae (scale : Scale) (predicate : Spatial → Prop)
    (almost : ∀ᵐ point ∂volume.restrict openUnitDisk, predicate point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, predicate (scale.val • point) :=
  ae_restrict_of_ae_restrict_of_subset (startupDilation_inclusion scale)
    (pull_ae openUnitDisk openUnitDisk_isOpen.measurableSet scale almost)

/-- Every SAME full integer-cell moment survives the physical change of coordinates. -/
theorem startupDilation_moment (scale : Scale) (power : ℕ) (field moment : StartupL2 3)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ power • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupDilation scale moment point cell =
        Grad.CellWeights.cellWeight cell ^ power • startupDilation scale field point cell := by
  filter_upwards [startupDilation_ae scale field, startupDilation_ae scale moment,
    startupDilation_pull_ae scale _ same] with point fieldAt momentAt sameAt
  intro cell
  rw [fieldAt, momentAt, sameAt cell]

/-- Physical dilation changes the argument of the SAME original phase,
without replacing its analytic width or radial square-root profile. -/
theorem startupDilation_weighted_same (sigma gamma : ℝ) (scale : Scale)
    (raw : ℤ → Spatial → PhysicalValue 3) (field : StartupL2 3)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma 1 cell point • raw cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupDilation scale field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma scale.val cell point • raw cell (scale.val • point) := by
  filter_upwards [startupDilation_ae scale field, startupDilation_pull_ae scale _ same] with point fieldAt sameAt
  intro cell
  rw [fieldAt, sameAt cell, ← startupPhysicalWeight_dilation sigma gamma scale.val scale.property.1.le]

end Grad.CartesianStartup
