import QS3SmoothRanges

noncomputable section

namespace Grad.RealFixedRanges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisCore
open Grad.SmoothingFamily Grad.Cor18 Grad.QuotientProjection Grad.CompletedReality

/-- COR23's exact real fixed-range construction. The maps are the actual
completed projections and literal involutions, not arbitrary supplied data. -/
def RealFixedRangeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade),
    IsClosed (stateRange parameters parameter inside grade large : Set (XAmbient parameters grade)) ∧
    IsClosed (sourceRange parameters grade large : Set (ZAmbient parameters grade)) ∧
    CompleteSpace (stateRange parameters parameter inside grade large) ∧
    CompleteSpace (sourceRange parameters grade large) ∧
    (∀ field : XAmbient parameters grade,
      field ∈ stateRange parameters parameter inside grade large ↔
        stateProjection parameters parameter inside grade large field = field ∧
        xConjugation parameters grade field = field) ∧
    (∀ field : ZAmbient parameters grade,
      field ∈ sourceRange parameters grade large ↔
        sourceProjection parameters grade large field = field ∧ zConjugation parameters grade field = field) ∧
    (∀ field : StateCore parameters,
      stateToGrade parameters grade field ∈ stateRange parameters parameter inside grade large ↔
        field ∈ stateSmoothRange parameters parameter inside) ∧
    (∀ field : SmoothQuotient parameters,
      quotientEta parameters grade field ∈ sourceRange parameters grade large ↔
        field ∈ sourceSmoothRange parameters) ∧
    (∀ field : stateSmoothRange parameters parameter inside,
      ‖stateSmoothEmbedding parameters parameter inside grade large field‖ =
        ‖stateToGrade parameters grade field.val‖) ∧
    (∀ field : sourceSmoothRange parameters,
      ‖sourceSmoothEmbedding parameters grade large field‖ = quotientNorm parameters grade field.val)

theorem actualRealFixedRanges : RealFixedRangeGoal := by
  intro parameters parameter inside grade large
  exact ⟨stateRange_closed parameters parameter inside grade large,
    sourceRange_closed parameters grade large, inferInstance, inferInstance,
    mem_stateRange parameters parameter inside grade large, mem_sourceRange parameters grade large,
    stateToGrade_mem_iff parameters parameter inside grade large, quotientEta_mem_iff parameters grade large,
    stateSmoothEmbedding_norm parameters parameter inside grade large, sourceSmoothEmbedding_norm parameters grade large⟩

end Grad.RealFixedRanges
