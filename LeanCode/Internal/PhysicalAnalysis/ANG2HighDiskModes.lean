import ANG1CompletedDiskModes

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
attribute [local instance] diskComplexNormedSpace

private theorem angular_selected_commute (mode : ℤ) (modes : Finset ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (selectedAngularJet modes field) =
      selectedAngularJet modes (angularClosedJet mode field) := by
  rw [angularClosedJet_selected, selectedAngularJet_eq]
  simp_rw [angularClosedJet_projection]
  simp [eq_comm]

private theorem angular_excluded_commute (mode : ℤ) (modes : Finset ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (excludedAngularJet modes field) =
      excludedAngularJet modes (angularClosedJet mode field) := by
  change angularClosedJetLinear 1 mode (field - selectedAngularJet modes field) = _
  rw [map_sub]
  change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet modes field) = _
  rw [angular_selected_commute]
  rfl

theorem diskAngularMode_high_mem (mode : ℤ) (field : highDiskGrade) :
    diskAngularMode mode field.val ∈ highDiskGrade := by
  apply isClosed_property highDiskCoreInto_denseRange
    (highDiskCore.range.isClosed_topologicalClosure.preimage
      ((diskAngularMode mode).continuous.comp highDiskGrade.subtypeL.continuous)) _ field
  intro core
  have equality : diskAngularMode mode (highDiskCoreInto core).val = highDiskCore (angularClosedJet mode core) :=
    (diskAngularMode_core mode (excludedAngularJet lowAngularModes core)).trans
      (congrArg diskCoreInto (angular_excluded_commute mode lowAngularModes core))
  exact (congrArg (fun point : diskGrade => point ∈ highDiskGrade) equality).mpr
    (Submodule.le_topologicalClosure _ ⟨angularClosedJet mode core, rfl⟩)

/-- All angular modes, including the zero low-mode operator, on high H1. -/
def highDiskMode (mode : ℤ) : highDiskGrade →L[ℂ] highDiskGrade :=
  ((diskAngularMode mode).comp highDiskGrade.subtypeL).codRestrict _ (diskAngularMode_high_mem mode)

theorem highDiskMode_bulk (mode : ℤ) (field : highDiskGrade) :
    highDiskBulk (highDiskMode mode field) = diskMode mode (highDiskBulk field) :=
  diskAngularMode_bulk mode field.val

theorem highDiskMode_core (mode : ℤ) (field : ClosedJet 1) :
    (highDiskMode mode (highDiskCoreInto field)).val =
      diskCoreInto (angularClosedJet mode (excludedAngularJet lowAngularModes field)) :=
  diskAngularMode_core mode _

theorem highDiskMode_projection (first second : ℤ) (field : highDiskGrade) :
    highDiskMode first (highDiskMode second field) =
      if first = second then highDiskMode first field else 0 := by
  apply highDiskBulk_injective
  have equality := (highDiskMode_bulk first (highDiskMode second field)).trans
    ((congrArg (diskMode first) (highDiskMode_bulk second field)).trans
      (diskMode_projection first second (highDiskBulk field)))
  refine equality.trans ?_
  split_ifs
  · exact (highDiskMode_bulk first field).symm
  · exact (highDiskBulk.map_zero).symm

theorem highDiskMode_low_zero (mode : ℤ) (low : mode ∈ lowAngularModes) (field : highDiskGrade) :
    highDiskMode mode field = 0 := by
  apply highDiskBulk_injective
  exact (highDiskMode_bulk mode field).trans
    ((highDiskBulk_spectral field mode low).trans highDiskBulk.map_zero.symm)

theorem highL2Mode_mem (mode : ℤ) (field : highDiskL2) : diskMode mode field.val ∈ highDiskL2 := by
  intro other low
  rw [diskMode_projection]
  split_ifs
  · exact field.property other low
  · rfl

def highL2Mode (mode : ℤ) : highDiskL2 →L[ℂ] highDiskL2 :=
  ((diskMode mode).comp highDiskL2.subtypeL).codRestrict _ (highL2Mode_mem mode)

theorem highDiskMode_highBulk (mode : ℤ) (field : highDiskGrade) :
    highBulkInto (highDiskMode mode field) = highL2Mode mode (highBulkInto field) :=
  Subtype.ext (highDiskMode_bulk mode field)

end Grad.CircularHighWeak
