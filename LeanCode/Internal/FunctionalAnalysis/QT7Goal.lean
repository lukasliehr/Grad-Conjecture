import QT6ActualCompletions

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.Constraints Grad.AxisCore Grad.SmoothingFamily
open Grad.QuotientProjection

/-- COR24: the identical smooth real fixed equations are dense in the
canonical completed carriers, with the inherited original grade norms;
their actual norm completions have exact core-preserving isometries. -/
def RealConstrainedDensityGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade),
    DenseRange (stateSmoothEmbedding parameters parameter inside grade large) ∧
    DenseRange (sourceSmoothEmbedding parameters grade large) ∧
    (∀ field : StateGradeCore parameters parameter inside grade large,
      ‖field‖ = ‖stateToGrade parameters grade field.toCore.val‖) ∧
    (∀ field : SourceGradeCore parameters grade large,
      ‖field‖ = quotientNorm parameters grade field.toCore.val) ∧
    (∃ equivalence : UniformSpace.Completion (StateGradeCore parameters parameter inside grade large)
        ≃ₗᵢ[ℝ] stateRange parameters parameter inside grade large,
      ∀ field : stateSmoothRange parameters parameter inside,
        equivalence (stateCoreToCompletion parameters parameter inside grade large field) =
          stateSmoothEmbedding parameters parameter inside grade large field) ∧
    (∃ equivalence : UniformSpace.Completion (SourceGradeCore parameters grade large)
        ≃ₗᵢ[ℝ] sourceRange parameters grade large,
      ∀ field : sourceSmoothRange parameters,
        equivalence (sourceCoreToCompletion parameters grade large field) =
          sourceSmoothEmbedding parameters grade large field)

theorem actualRealConstrainedDensity : RealConstrainedDensityGoal := by
  intro parameters parameter inside grade large
  exact ⟨stateSmoothEmbedding_denseRange parameters parameter inside grade large,
    sourceSmoothEmbedding_denseRange parameters grade large,
    stateGradeCore_norm parameters parameter inside grade large,
    sourceGradeCore_norm parameters grade large,
    ⟨stateCompletionEquiv parameters parameter inside grade large,
      stateCompletionEquiv_core parameters parameter inside grade large⟩,
    ⟨sourceCompletionEquiv parameters grade large, sourceCompletionEquiv_core parameters grade large⟩⟩

end Grad.RealFixedRanges
