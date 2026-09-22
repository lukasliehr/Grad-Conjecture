import QW8GradeCompatibility

noncomputable section

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

/-- COR28: actual completed real constrained N18 equivalences with both
same-grade bounds, exact core law, reverse, identity, cocycle and inclusions. -/
def CompletedTransferGoal : Prop :=
  ∀ (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade),
    (∀ field : stateSmoothRange parameters first insideFirst,
      completedTransferEquiv parameters first insideFirst second insideSecond grade large
        (stateSmoothEmbedding parameters first insideFirst grade large field) =
          stateSmoothEmbedding parameters second insideSecond grade large
            (coreTransferEquiv parameters first insideFirst second insideSecond field)) ∧
    (∀ field : stateRange parameters first insideFirst grade large,
      ‖completedTransferEquiv parameters first insideFirst second insideSecond grade large field‖ ≤
        transferConstant parameters first second grade * ‖field‖) ∧
    (∀ field : stateRange parameters second insideSecond grade large,
      ‖(completedTransferEquiv parameters first insideFirst second insideSecond grade large).symm field‖ ≤
        transferConstant parameters second first grade * ‖field‖) ∧
    (completedTransferEquiv parameters first insideFirst second insideSecond grade large).symm =
      completedTransferEquiv parameters second insideSecond first insideFirst grade large ∧
    (∀ field : stateRange parameters first insideFirst grade large,
      completedTransferEquiv parameters first insideFirst first insideFirst grade large field = field) ∧
    (∀ (third : Seed.Parameters) (insideThird : third ∈ Seed.parameterDomain)
      (field : stateRange parameters first insideFirst grade large),
      completedTransferEquiv parameters second insideSecond third insideThird grade large
        (completedTransferEquiv parameters first insideFirst second insideSecond grade large field) =
          completedTransferEquiv parameters first insideFirst third insideThird grade large field) ∧
    (∀ (upper : ℕ) (ordered : grade ≤ upper)
      (field : stateRange parameters first insideFirst upper (large.trans ordered)),
      stateLowering parameters second insideSecond large ordered
        (completedTransferEquiv parameters first insideFirst second insideSecond upper (large.trans ordered) field) =
          completedTransferEquiv parameters first insideFirst second insideSecond grade large
            (stateLowering parameters first insideFirst large ordered field))

theorem actualCompletedTransfer : CompletedTransferGoal := by
  intro parameters first insideFirst second insideSecond grade large
  exact ⟨completedTransferEquiv_core parameters first insideFirst second insideSecond grade large,
    completedTransferEquiv_bound parameters first insideFirst second insideSecond grade large,
    completedTransferEquiv_reverse_bound parameters first insideFirst second insideSecond grade large,
    completedTransferEquiv_symm parameters first insideFirst second insideSecond grade large,
    completedTransfer_self parameters first insideFirst grade large,
    fun third insideThird => completedTransfer_cocycle parameters first insideFirst second insideSecond third insideThird grade large,
    fun _ ordered => completedTransferEquiv_lowering parameters first insideFirst second insideSecond large ordered⟩

/-- The coherent full COR27/COR28 seed-transfer boundary. -/
theorem actualSeedTransfer : CoreTransferGoal ∧ CompletedTransferGoal :=
  ⟨actualCoreTransfer, actualCompletedTransfer⟩

end Grad.ConstrainedTransfer
