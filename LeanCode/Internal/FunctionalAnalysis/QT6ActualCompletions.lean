import QT5CompletionIsometry

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.Constraints Grad.AxisCore Grad.SmoothingFamily
open Grad.QuotientProjection

def stateGradeEmbedding (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    StateGradeCore parameters parameter inside grade large →ₗᵢ[ℝ]
      stateRange parameters parameter inside grade large :=
  NormedCoreCopy.isometricEmbedding _ _

def sourceGradeEmbedding (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    SourceGradeCore parameters grade large →ₗᵢ[ℝ] sourceRange parameters grade large :=
  NormedCoreCopy.isometricEmbedding _ _

theorem stateGradeEmbedding_denseRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (stateGradeEmbedding parameters parameter inside grade large) :=
  NormedCoreCopy.isometricEmbedding_denseRange
    (stateSmoothEmbedding_denseRange parameters parameter inside grade large)

theorem sourceGradeEmbedding_denseRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (sourceGradeEmbedding parameters grade large) :=
  NormedCoreCopy.isometricEmbedding_denseRange (sourceSmoothEmbedding_denseRange parameters grade large)

def stateCoreToCompletion (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateSmoothRange parameters parameter inside →ₗ[ℝ]
      UniformSpace.Completion (StateGradeCore parameters parameter inside grade large) :=
  (UniformSpace.Completion.toComplₗᵢ : StateGradeCore parameters parameter inside grade large →ₗᵢ[ℝ]
    UniformSpace.Completion (StateGradeCore parameters parameter inside grade large)).toLinearMap.comp
      (NormedCoreCopy.ofCore _ _)

def sourceCoreToCompletion (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    sourceSmoothRange parameters →ₗ[ℝ] UniformSpace.Completion (SourceGradeCore parameters grade large) :=
  (UniformSpace.Completion.toComplₗᵢ : SourceGradeCore parameters grade large →ₗᵢ[ℝ]
    UniformSpace.Completion (SourceGradeCore parameters grade large)).toLinearMap.comp
      (NormedCoreCopy.ofCore _ _)

/-- Completion of the literal smooth real constrained state core, in the
original grade norm (including the axis shift q+1). -/
def stateCompletionEquiv (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    UniformSpace.Completion (StateGradeCore parameters parameter inside grade large) ≃ₗᵢ[ℝ]
      stateRange parameters parameter inside grade large :=
  completionEquiv (stateGradeEmbedding parameters parameter inside grade large)
    (stateGradeEmbedding_denseRange parameters parameter inside grade large)

/-- Completion of the literal smooth real constrained quotient core, in
the original fourfold Hilbert norm. -/
def sourceCompletionEquiv (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    UniformSpace.Completion (SourceGradeCore parameters grade large) ≃ₗᵢ[ℝ]
      sourceRange parameters grade large :=
  completionEquiv (sourceGradeEmbedding parameters grade large)
    (sourceGradeEmbedding_denseRange parameters grade large)

theorem stateCompletionEquiv_core (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters parameter inside) :
    stateCompletionEquiv parameters parameter inside grade large
      (stateCoreToCompletion parameters parameter inside grade large field) =
        stateSmoothEmbedding parameters parameter inside grade large field :=
  completionEquiv_eta _ _ (NormedCoreCopy.ofCore _ _ field)

theorem sourceCompletionEquiv_core (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : sourceSmoothRange parameters) :
    sourceCompletionEquiv parameters grade large (sourceCoreToCompletion parameters grade large field) =
      sourceSmoothEmbedding parameters grade large field :=
  completionEquiv_eta _ _ (NormedCoreCopy.ofCore _ _ field)

theorem stateGradeCore_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateGradeCore parameters parameter inside grade large) :
    ‖field‖ = ‖stateToGrade parameters grade field.toCore.val‖ := rfl

theorem sourceGradeCore_norm (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : SourceGradeCore parameters grade large) :
    ‖field‖ = quotientNorm parameters grade field.toCore.val := rfl

end Grad.RealFixedRanges
