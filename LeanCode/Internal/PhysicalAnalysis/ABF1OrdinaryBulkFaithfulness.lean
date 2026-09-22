import AOG3ActualFiniteGlobalConsumer
import APF2CompletedInsertion

noncomputable section
open scoped ContDiff
namespace Grad.OrdinaryDiskFaithfulness
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.OrdinaryDiskReconstruction Grad.OrdinaryDiskForward Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

/-- The literal disk bulk determines every ordinary Sobolev representative.
This uses the accepted injective original-grade inclusion and exact retraction. -/
theorem ordinaryBulk_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (unitDiskBulk grade) := by
  intro first second same
  have inserted : ordinaryInsertion parameters grade first = ordinaryInsertion parameters grade second := by
    apply completedInclusion_injective parameters (Nat.zero_le grade)
    exact (ordinaryInsertion_zero_coherent parameters grade first).trans
      ((congrArg (Grad.InteriorPeriodization.diskOriginalZero parameters) same).trans
        (ordinaryInsertion_zero_coherent parameters grade second).symm)
  exact (originalDisk_insertion parameters grade first).symm.trans
    ((congrArg (originalDisk parameters grade) inserted).trans
      (originalDisk_insertion parameters grade second))

theorem ordinaryLower_same_bulk (parameters : PhaseParameters) {low high : ℕ} (ordered : low ≤ high)
    (lower : unitDiskSobolev low) (upper : unitDiskSobolev high)
    (same : unitDiskBulk high upper = unitDiskBulk low lower) :
    unitLower ordered upper = lower :=
  ordinaryBulk_injective parameters low ((unitLower_bulk ordered upper).trans same)

/-- Any grade-indexed family representing one literal disk field is already
compatible under the actual ordinary lowering maps. -/
theorem ordinaryFamily_compatible (parameters : PhaseParameters)
    (family : (grade : ℕ) → unitDiskSobolev grade) (bulk : DiskL2 1)
    (same : ∀ grade, unitDiskBulk grade (family grade) = bulk)
    (low high : ℕ) (ordered : low ≤ high) :
    unitLower ordered (family high) = family low :=
  ordinaryLower_same_bulk parameters ordered (family low) (family high)
    ((same high).trans (same low).symm)

end Grad.OrdinaryDiskFaithfulness
