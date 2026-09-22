import AKDM3OriginalPureCellNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set MeasureTheory

namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers
open Grad.CartesianStartup Grad.PDEBootstrap

/-- A core recovered from the same punctured solution has exactly the
native pure-cell norm; the exceptional axis has zero measure. -/
theorem originalCellNorm_eq_recoveredMoment {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (moments : StartupAllMoments dimension)
    (physical : ℤ → Spatial → PhysicalValue dimension)
    (coreSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
      (core.val cell).value point = physical cell point.val)
    (momentSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moments.field point cell = cartesianWeight parameters cell point • physical cell point)
    (grade : ℕ) : originalCellNorm parameters grade core = ‖moments.moment grade‖ := by
  apply originalCellNorm_eq_actualMoment_of_ae parameters core moments
  filter_upwards [momentSame,startupDisk_ae_nonzero,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point weighted nonzero inside
  intro cell
  have closed : point ∈ closedUnitDisk := openDiskMembershipClosed point inside
  rw [closedMultiDerivative_zero,closedDiskLift,dif_pos closed,phaseWeightedJet_value]
  rw [coreSame ⟨point,closed⟩ (norm_pos_iff.mpr nonzero) cell]
  exact weighted cell

end Grad.OriginalCartesianTameEstimate
