import QW7CompletedEquivalence

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

/-- The two orders of seed transfer and canonical grade inclusion agree
on the entire actual source slice, by their exact common dense-core law. -/
theorem completedTransfer_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateRange parameters first insideFirst upper (large.trans ordered)) :
    stateLowering parameters second insideSecond large ordered
      (completedTransfer parameters first insideFirst second insideSecond upper (large.trans ordered) field) =
        completedTransfer parameters first insideFirst second insideSecond lower large
          (stateLowering parameters first insideFirst large ordered field) := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters first insideFirst upper (large.trans ordered))
    (isClosed_eq ((stateLowering parameters second insideSecond large ordered).continuous.comp
      (completedTransfer parameters first insideFirst second insideSecond upper (large.trans ordered)).continuous)
      ((completedTransfer parameters first insideFirst second insideSecond lower large).continuous.comp
        (stateLowering parameters first insideFirst large ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [completedTransfer_core, stateLowering_core, stateLowering_core, completedTransfer_core]

theorem completedTransferEquiv_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateRange parameters first insideFirst upper (large.trans ordered)) :
    stateLowering parameters second insideSecond large ordered
      (completedTransferEquiv parameters first insideFirst second insideSecond upper (large.trans ordered) field) =
        completedTransferEquiv parameters first insideFirst second insideSecond lower large
          (stateLowering parameters first insideFirst large ordered field) :=
  completedTransfer_lowering parameters first insideFirst second insideSecond large ordered field

theorem completedTransferEquiv_reverse_bound (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateRange parameters second insideSecond grade large) :
    ‖(completedTransferEquiv parameters first insideFirst second insideSecond grade large).symm field‖ ≤
      transferConstant parameters second first grade * ‖field‖ := by
  rw [completedTransferEquiv_symm]
  exact completedTransferEquiv_bound parameters second insideSecond first insideFirst grade large field

end Grad.ConstrainedTransfer
