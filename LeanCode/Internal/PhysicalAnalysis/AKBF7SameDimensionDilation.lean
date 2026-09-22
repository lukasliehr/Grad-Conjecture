import AKBF6OriginalFixedCellMoments
import AKAY20SameFieldDilation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.SpatialDilation

/-- The existing exact inward dilation followed by existing restriction. -/
def startupMomentDilation {dimension : ℕ} (scale : Scale) (field : StartupL2 dimension) : StartupL2 dimension :=
  Restriction.fieldRestriction (Grad.GenericCarriers.CellValues dimension) (startupDilation_inclusion scale)
    (rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field)

theorem startupMomentDilation_norm {dimension : ℕ} (scale : Scale) (field : StartupL2 dimension) :
    ‖startupMomentDilation scale field‖ ≤ scale.val⁻¹ * ‖field‖ :=
  (Restriction.fieldRestriction_norm_le (Grad.GenericCarriers.CellValues dimension) (startupDilation_inclusion scale)
    (rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field)).trans_eq
      (rawValue_norm dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field)

theorem startupMomentDilation_ae {dimension : ℕ} (scale : Scale) (field : StartupL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, startupMomentDilation scale field point = field (scale.val • point) := by
  exact (Restriction.fieldRestriction_ae (Grad.GenericCarriers.CellValues dimension) (startupDilation_inclusion scale)
    (rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field)).trans
    (ae_restrict_of_ae_restrict_of_subset (startupDilation_inclusion scale)
      (rawValue_ae dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field))

/-- Every SAME full integer-cell moment survives the physical change of coordinates. -/
theorem startupMomentDilation_moment {dimension : ℕ} (scale : Scale) (power : ℕ) (field moment : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ power • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupMomentDilation scale moment point cell =
        Grad.CellWeights.cellWeight cell ^ power • startupMomentDilation scale field point cell := by
  filter_upwards [startupMomentDilation_ae scale field, startupMomentDilation_ae scale moment,
    startupDilation_pull_ae scale _ same] with point fieldAt momentAt sameAt
  intro cell
  rw [fieldAt, momentAt, sameAt cell]

/-- Physical dilation changes the argument of the SAME original phase,
without replacing its analytic width or radial square-root profile. -/
theorem startupMomentDilation_weighted_same {dimension : ℕ} (sigma gamma : ℝ) (scale : Scale)
    (raw : ℤ → Spatial → PhysicalValue dimension) (field : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma 1 cell point • raw cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupMomentDilation scale field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma scale.val cell point • raw cell (scale.val • point) := by
  filter_upwards [startupMomentDilation_ae scale field, startupDilation_pull_ae scale _ same] with point fieldAt sameAt
  intro cell
  rw [fieldAt, sameAt cell, ← startupPhysicalWeight_dilation sigma gamma scale.val scale.property.1.le]

def StartupMoments.dilate {dimension : ℕ} (family : StartupMoments dimension) (scale : Scale) : StartupMoments dimension where
  field := startupMomentDilation scale family.field
  moment grade := startupMomentDilation scale (family.moment grade)
  zero := congrArg (startupMomentDilation scale) family.zero
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact startupMomentDilation_moment scale grade.val family.field (family.moment grade)
      (family.same.mono (fun _ same => same grade))

def originalStartupScale (length : ℝ) (positive : 0 < length) : Scale :=
  ⟨min 1 length / 4, by constructor; positivity; exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (by norm_num)⟩

end Grad.CartesianStartup
