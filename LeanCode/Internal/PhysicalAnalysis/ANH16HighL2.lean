import ANH14DiskMultiplier

noncomputable section
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- The actual full-disk L2 subspace with precisely the five low angular
coefficients removed. The coefficients are those of the physical rotations. -/
def highDiskL2 : Submodule ℂ (DiskL2 1) where
  carrier := {field | ∀ mode ∈ lowAngularModes, diskMode mode field = 0}
  zero_mem' := by simp
  add_mem' := by intro first second hfirst hsecond mode low; simp [hfirst mode low, hsecond mode low]
  smul_mem' := by intro scalar field high mode low; simp [high mode low]

def highL2Projection : DiskL2 1 →L[ℂ] DiskL2 1 :=
  ContinuousLinearMap.id ℂ _ - ∑ mode ∈ lowAngularModes, diskMode mode

theorem highL2Projection_apply (field : DiskL2 1) :
    highL2Projection field = field - ∑ mode ∈ lowAngularModes, diskMode mode field := by
  simp only [highL2Projection, sub_apply, ContinuousLinearMap.id_apply,
    sum_apply]

theorem highL2Projection_mem (field : DiskL2 1) : highL2Projection field ∈ highDiskL2 := by
  intro mode low
  rw [highL2Projection_apply, map_sub, map_sum]
  simp_rw [diskMode_projection]
  simp [low]

theorem highL2Projection_fixed (field : highDiskL2) : highL2Projection field.val = field.val := by
  rw [highL2Projection_apply]
  have vanish : (∑ mode ∈ lowAngularModes, diskMode mode field.val) = 0 :=
    Finset.sum_eq_zero (fun mode low => field.property mode low)
  rw [vanish, sub_zero]

theorem highL2Projection_core (field : ClosedJet 1) :
    highL2Projection (closedL2Core field) = closedL2Core (excludedAngularJet lowAngularModes field) := by
  rw [highL2Projection_apply]
  change _ = closedL2Core (field - selectedAngularJet lowAngularModes field)
  rw [map_sub, selectedAngularJet_eq, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mode _
  exact diskMode_core mode field

def highL2Core : ClosedJet 1 →ₗ[ℂ] highDiskL2 :=
  (highL2Projection.toLinearMap.comp closedL2Core).codRestrict _ (fun _ => highL2Projection_mem _)

def highL2ProjectionInto : DiskL2 1 →L[ℂ] highDiskL2 :=
  highL2Projection.codRestrict _ highL2Projection_mem

theorem highL2ProjectionInto_surjective : Function.Surjective highL2ProjectionInto := by
  intro field
  exact ⟨field.val, Subtype.ext (highL2Projection_fixed field)⟩

/-- Thus this spectral L2 space is exactly the completion of the physical
smooth high core, with no additional vanishing or boundary condition. -/
theorem highL2Core_denseRange : DenseRange highL2Core :=
  highL2ProjectionInto_surjective.denseRange.comp closedL2Core_denseRange highL2ProjectionInto.continuous

def highBulkInto : highDiskGrade →L[ℂ] highDiskL2 :=
  highDiskBulk.codRestrict _ highDiskBulk_spectral

end Grad.CircularHighWeak
