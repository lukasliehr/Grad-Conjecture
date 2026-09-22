import APR1OriginalDiskCore

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion

abbrev ordinaryDiskNormedSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) :=
  (unitDiskSobolev grade).normedSpace
attribute [local instance] ordinaryDiskNormedSpace

instance ordinaryDisk_complete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

/-- Actual original-grade completion to ordinary disk H^q, by the literal
phase-weighted coefficient at cell zero and its proved constant-one bound. -/
def originalDisk (parameters : PhaseParameters) (grade : ℕ) :
    AGrade parameters 1 grade →L[ℂ] unitDiskSobolev grade :=
  @denseCoreExtension 1 grade parameters (unitDiskSobolev grade)
    (inferInstance : NormedAddCommGroup (unitDiskSobolev grade))
    (ordinaryDiskNormedSpace grade) (ordinaryDisk_complete grade)
    (originalDiskCore parameters grade) 1 (originalDiskCore_bound parameters grade)

theorem originalDisk_core (parameters : PhaseParameters) (grade : ℕ)
    (field : GradeCore parameters 1 grade) :
    originalDisk parameters grade (aGradeEta parameters field) =
      unitDiskCoreInto grade (phaseZeroCore parameters grade field) :=
  @denseCoreExtension_apply_eta 1 grade parameters (unitDiskSobolev grade)
    (inferInstance : NormedAddCommGroup (unitDiskSobolev grade))
    (ordinaryDiskNormedSpace grade) (ordinaryDisk_complete grade)
    (originalDiskCore parameters grade) 1 (originalDiskCore_bound parameters grade) field

theorem originalDisk_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 1 grade) :
    ‖originalDisk parameters grade field‖ ≤ ‖field‖ :=
  (@denseCoreExtension_apply_norm_le 1 grade parameters (unitDiskSobolev grade)
    (inferInstance : NormedAddCommGroup (unitDiskSobolev grade))
    (ordinaryDiskNormedSpace grade) (ordinaryDisk_complete grade)
    (originalDiskCore parameters grade) 1 (originalDiskCore_bound parameters grade) field).trans_eq (one_mul _)

theorem originalDisk_core_bulk (parameters : PhaseParameters) (grade : ℕ)
    (field : GradeCore parameters 1 grade) :
    unitDiskBulk grade (originalDisk parameters grade (aGradeEta parameters field)) =
      closedL2Core (phaseWeightedJet parameters 0 (field.toCore.val 0)) :=
  (congrArg (unitDiskBulk grade) (originalDisk_core parameters grade field)).trans
    (unitDiskBulk_core grade (phaseZeroCore parameters grade field))

/-- All grades realize the same original disk L2 field. -/
theorem originalDisk_bulk_coherent (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 1 grade) :
    unitDiskBulk grade (originalDisk parameters grade field) =
      unitDiskBulk 0 (originalDisk parameters 0 (completedInclusion parameters (Nat.zero_le grade) field)) := by
  apply isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_eq ((unitDiskBulk grade).continuous.comp (originalDisk parameters grade).continuous)
      ((unitDiskBulk 0).continuous.comp ((originalDisk parameters 0).continuous.comp
        (completedInclusion parameters (Nat.zero_le grade)).continuous))) _ field
  intro core
  have second := (congrArg (fun value : AGrade parameters 1 0 => unitDiskBulk 0 (originalDisk parameters 0 value))
    (completedInclusion_apply_eta parameters (Nat.zero_le grade) core)).trans
      (originalDisk_core_bulk parameters 0 (GradeCore.ofCoreLinear core.toCore))
  exact (originalDisk_core_bulk parameters grade core).trans second.symm

end Grad.OrdinaryDiskReconstruction
