import QW9Goal

noncomputable section

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore

/-- A concrete project consumer: a continuous real linear equivalence on
the original completed slices, with the exact N18 smooth-core equation. -/
theorem actualCompletedSeedTransfer_exists (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ transfer : stateRange parameters first insideFirst grade large ≃L[ℝ]
        stateRange parameters second insideSecond grade large,
      (∀ field : stateSmoothRange parameters first insideFirst,
        transfer (stateSmoothEmbedding parameters first insideFirst grade large field) =
          stateSmoothEmbedding parameters second insideSecond grade large
            (coreTransferEquiv parameters first insideFirst second insideSecond field)) ∧
      (∀ field, ‖transfer field‖ ≤ transferConstant parameters first second grade * ‖field‖) := by
  have proof := actualCompletedTransfer parameters first insideFirst second insideSecond grade large
  exact ⟨completedTransferEquiv parameters first insideFirst second insideSecond grade large, proof.1, proof.2.1⟩

/-- Uniqueness against any separately constructed actual ambient N18 map.
This is a comparison tool, not an assumed construction or range condition:
the constrained equivalence already exists unconditionally above. -/
theorem completedTransfer_ambient_agreement (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (ambient : XAmbient parameters grade → XAmbient parameters grade) (continuous : Continuous ambient)
    (coreLaw : ∀ field : stateSmoothRange parameters first insideFirst,
      ambient (stateToGrade parameters grade field.val) =
        stateToGrade parameters grade (coreTransfer parameters first insideFirst second insideSecond field.val))
    (field : stateRange parameters first insideFirst grade large) :
    ambient field.val = (completedTransfer parameters first insideFirst second insideSecond grade large field).val := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters first insideFirst grade large)
    (isClosed_eq (continuous.comp (stateInclusion parameters first insideFirst grade large).continuous)
      ((stateInclusion parameters second insideSecond grade large).continuous.comp
        (completedTransfer parameters first insideFirst second insideSecond grade large).continuous)) ?_ field
  intro core
  change ambient (stateToGrade parameters grade core.val) =
    (completedTransfer parameters first insideFirst second insideSecond grade large
      (stateSmoothEmbedding parameters first insideFirst grade large core)).val
  rw [completedTransfer_core]
  exact coreLaw core

end Grad.ConstrainedTransfer
