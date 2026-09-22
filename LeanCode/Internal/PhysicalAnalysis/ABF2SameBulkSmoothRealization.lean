import ABF1OrdinaryBulkFaithfulness
import COR16Compatible

noncomputable section
namespace Grad.OrdinaryDiskFaithfulness
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.OrdinaryDiskReconstruction Grad.OrdinaryDiskForward Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

/-- The accepted inverse-phase insertion converts a same-bulk ordinary family
into the actual compatible original grade family, before smooth reconstruction. -/
def sameBulkOriginalFamily (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk) : CompatibleAGrades parameters 1 :=
  ⟨fun grade => ordinaryInsertion parameters grade (family grade), by
    intro low high ordered
    apply completedInclusion_injective parameters (Nat.zero_le low)
    have composition := DFunLike.congr_fun
      (completedInclusion_comp (dimension := 1) parameters ordered (Nat.zero_le low))
      (ordinaryInsertion parameters high (family high))
    exact composition.trans ((ordinaryInsertion_zero_coherent parameters high (family high)).trans
      ((congrArg (Grad.InteriorPeriodization.diskOriginalZero parameters)
        ((same high).trans (same low).symm)).trans
        (ordinaryInsertion_zero_coherent parameters low (family low)).symm))⟩

/-- A single genuine closed jet representing every grade of the same ordinary
Sobolev family, constructed through the accepted COR16 smooth reconstruction. -/
def sameBulkClosedJet (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk) : ClosedJet 1 :=
  phaseWeightedJet parameters 0
    ((compatibleToCore parameters (sameBulkOriginalFamily parameters family bulk same)).val 0)

theorem sameBulkClosedJet_core (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk) (grade : ℕ) :
    unitDiskCoreInto grade (sameBulkClosedJet parameters family bulk same) = family grade := by
  have realization := compatibleToCore_component parameters
    (sameBulkOriginalFamily parameters family bulk same) grade
  have mapped := congrArg (originalDisk parameters grade) realization
  have fromCore : originalDisk parameters grade
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
        (compatibleToCore parameters (sameBulkOriginalFamily parameters family bulk same)))) =
      unitDiskCoreInto grade (sameBulkClosedJet parameters family bulk same) :=
    originalDisk_core parameters grade (GradeCore.ofCoreLinear (grade := grade)
      (compatibleToCore parameters (sameBulkOriginalFamily parameters family bulk same)))
  exact fromCore.symm.trans (mapped.trans (originalDisk_insertion parameters grade (family grade)))

theorem sameBulkClosedJet_bulk (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk) :
    closedL2Core (sameBulkClosedJet parameters family bulk same) = bulk :=
  (unitDiskBulk_core 0 _).symm.trans
    ((congrArg (unitDiskBulk 0) (sameBulkClosedJet_core parameters family bulk same 0)).trans (same 0))

/-- Original-norm all-grade smooth realization, with each core injection exact. -/
theorem actualOrdinarySmoothRealization (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk) :
    ∃ core : ClosedJet 1, closedL2Core core = bulk ∧
      ∀ grade, unitDiskCoreInto grade core = family grade :=
  ⟨sameBulkClosedJet parameters family bulk same, sameBulkClosedJet_bulk parameters family bulk same,
    sameBulkClosedJet_core parameters family bulk same⟩

end Grad.OrdinaryDiskFaithfulness
