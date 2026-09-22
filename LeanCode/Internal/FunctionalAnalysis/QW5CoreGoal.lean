import QW4CoreEquivalence

noncomputable section

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.RealFixedRanges Grad.SmoothingFamily

/-- COR27: actual N18 core equivalences, with the literal formula, reverse
inverse, same-grade bound, identity and three-seed cocycle. -/
def CoreTransferGoal : Prop :=
  ∀ (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain),
    (∀ field : stateSmoothRange parameters first insideFirst,
      (coreTransferEquiv parameters first insideFirst second insideSecond field).val =
        (field.val.1, seedTransfer parameters first insideFirst second insideSecond field.val.2.1, field.val.2.2)) ∧
    (∀ (grade : ℕ) (field : stateSmoothRange parameters first insideFirst),
      ‖stateToGrade parameters grade (coreTransferEquiv parameters first insideFirst second insideSecond field).val‖ ≤
        transferConstant parameters first second grade * ‖stateToGrade parameters grade field.val‖) ∧
    (∀ field : stateSmoothRange parameters second insideSecond,
      (coreTransferEquiv parameters first insideFirst second insideSecond).symm field =
        coreTransferEquiv parameters second insideSecond first insideFirst field) ∧
    (∀ field : stateSmoothRange parameters first insideFirst,
      coreTransferEquiv parameters first insideFirst first insideFirst field = field) ∧
    (∀ (third : Seed.Parameters) (insideThird : third ∈ Seed.parameterDomain)
      (field : stateSmoothRange parameters first insideFirst),
      coreTransferEquiv parameters second insideSecond third insideThird
        (coreTransferEquiv parameters first insideFirst second insideSecond field) =
          coreTransferEquiv parameters first insideFirst third insideThird field)

theorem actualCoreTransfer : CoreTransferGoal := by
  intro parameters first insideFirst second insideSecond
  exact ⟨coreTransferEquiv_apply parameters first insideFirst second insideSecond,
    coreTransferEquiv_bound parameters first insideFirst second insideSecond,
    coreTransferEquiv_symm_apply parameters first insideFirst second insideSecond,
    constrainedCoreTransfer_self parameters first insideFirst,
    constrainedCoreTransfer_cocycle parameters first insideFirst second insideSecond⟩

/-- Immediate completed-carrier consumer: the exact transferred smooth
field embeds in the actual target slice and returns under the reverse map. -/
theorem coreTransfer_embedded_reverse (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (field : stateSmoothRange parameters first insideFirst) :
    stateSmoothEmbedding parameters first insideFirst grade large
      ((coreTransferEquiv parameters first insideFirst second insideSecond).symm
        (coreTransferEquiv parameters first insideFirst second insideSecond field)) =
          stateSmoothEmbedding parameters first insideFirst grade large field := by
  rw [LinearEquiv.symm_apply_apply]

end Grad.ConstrainedTransfer
