import APF1OriginalGradeInsertion
import APR2CompletedOrdinaryDisk
import AIP2ActualDiskFourier

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskForward
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.OrdinaryDiskReconstruction Grad.InteriorPeriodization
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] ordinaryDiskNormedSpace

private theorem ordinaryInsertion_exists (parameters : PhaseParameters) (grade : ℕ) :
    ∃ insertion : unitDiskSobolev grade →L[ℂ] AGrade parameters 1 grade,
      (∀ core, insertion (unitDiskCoreInto grade core) = normalizedGradeCoreInto parameters grade core) ∧
      (∀ field, ‖insertion field‖ ≤ 1 * ‖field‖) :=
  @apDense_extension (ClosedJet 1) (unitDiskSobolev grade) (AGrade parameters 1 grade)
    inferInstance inferInstance (inferInstance : NormedAddCommGroup (unitDiskSobolev grade))
    (ordinaryDiskNormedSpace grade) (inferInstance : NormedAddCommGroup (AGrade parameters 1 grade))
    inferInstance inferInstance (unitDiskCoreInto grade) (ordinaryCore_injective grade)
    (unitDiskCoreInto_denseRange grade) (normalizedGradeCoreInto parameters grade) 1 zero_le_one
    (fun core => (normalizedGradeCoreInto_norm parameters grade core).le.trans_eq (one_mul _).symm)

/-- Isometric original inverse-phase single-cell insertion at every ordinary
Sobolev grade, constructed from the actual dense closed-jet cores. -/
def ordinaryInsertion (parameters : PhaseParameters) (grade : ℕ) :
    unitDiskSobolev grade →L[ℂ] AGrade parameters 1 grade :=
  (ordinaryInsertion_exists parameters grade).choose

theorem ordinaryInsertion_core (parameters : PhaseParameters) (grade : ℕ) (core : ClosedJet 1) :
    ordinaryInsertion parameters grade (unitDiskCoreInto grade core) =
      normalizedGradeCoreInto parameters grade core :=
  (ordinaryInsertion_exists parameters grade).choose_spec.1 core

theorem ordinaryInsertion_norm (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade) :
    ‖ordinaryInsertion parameters grade field‖ = ‖field‖ := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq (continuous_norm.comp (ordinaryInsertion parameters grade).continuous) continuous_norm) _ field
  intro core
  exact (congrArg norm (ordinaryInsertion_core parameters grade core)).trans (normalizedGradeCoreInto_norm parameters grade core)

theorem originalDisk_insertion (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade) :
    originalDisk parameters grade (ordinaryInsertion parameters grade field) = field := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((originalDisk parameters grade).continuous.comp (ordinaryInsertion parameters grade).continuous) continuous_id) _ field
  intro core
  exact (congrArg (originalDisk parameters grade) (ordinaryInsertion_core parameters grade core)).trans
    ((originalDisk_core parameters grade (normalizedGradeCore parameters grade core)).trans
      (congrArg (unitDiskCoreInto grade) (normalizedGradeCore_phase parameters grade core)))

/-- Grade-zero coherence uses the actual disk bulk and the accepted AIP
insertion; no pointwise phase-zero assumption or substitute lower norm. -/
theorem ordinaryInsertion_zero_coherent (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) :
    completedInclusion parameters (Nat.zero_le grade) (ordinaryInsertion parameters grade field) =
      diskOriginalZero parameters (unitDiskBulk grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((completedInclusion parameters (Nat.zero_le grade)).continuous.comp (ordinaryInsertion parameters grade).continuous)
      ((diskOriginalZero parameters).continuous.comp (unitDiskBulk grade).continuous)) _ field
  intro core
  have first := (congrArg (completedInclusion parameters (Nat.zero_le grade))
    (ordinaryInsertion_core parameters grade core)).trans
      (completedInclusion_apply_eta parameters (Nat.zero_le grade) (normalizedGradeCore parameters grade core))
  have second := (congrArg (diskOriginalZero parameters) (unitDiskBulk_core grade core)).trans
    (diskOriginalZero_core parameters core)
  exact first.trans second.symm

end Grad.OrdinaryDiskForward
