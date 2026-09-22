import QV3SimultaneousReconstruction

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.QuotientProjection

theorem reconstructedState_mem (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    reconstructedState parameters parameter inside family ∈ stateSmoothRange parameters parameter inside := by
  apply (stateToGrade_mem_iff parameters parameter inside 3 (le_refl 3) _).1
  have equality := (reconstructedState_grade parameters parameter inside family 3).trans
    (extendedState_at parameters parameter inside family ⟨3, le_refl 3⟩)
  rw [equality]
  exact (family.val ⟨3, le_refl 3⟩).property

theorem reconstructedSource_mem (parameters : PhaseParameters) (family : CompatibleSources parameters) :
    reconstructedSource parameters family ∈ sourceSmoothRange parameters := by
  apply (quotientEta_mem_iff parameters 3 (le_refl 3) _).1
  have equality := (reconstructedSource_grade parameters family 3).trans
    (extendedSource_at parameters family ⟨3, le_refl 3⟩)
  rw [equality]
  exact (family.val ⟨3, le_refl 3⟩).property

def reconstructedConstrainedState (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    stateSmoothRange parameters parameter inside :=
  ⟨reconstructedState parameters parameter inside family, reconstructedState_mem parameters parameter inside family⟩

def reconstructedConstrainedSource (parameters : PhaseParameters) (family : CompatibleSources parameters) :
    sourceSmoothRange parameters := ⟨reconstructedSource parameters family, reconstructedSource_mem parameters family⟩

theorem stateToCompatible_reconstructed (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    stateToCompatible parameters parameter inside (reconstructedConstrainedState parameters parameter inside family) =
      family := by
  apply Subtype.ext
  funext grade
  apply Subtype.ext
  exact (reconstructedState_grade parameters parameter inside family grade.val).trans
    (extendedState_at parameters parameter inside family grade)

theorem sourceToCompatible_reconstructed (parameters : PhaseParameters) (family : CompatibleSources parameters) :
    sourceToCompatible parameters (reconstructedConstrainedSource parameters family) = family := by
  apply Subtype.ext
  funext grade
  apply Subtype.ext
  exact (reconstructedSource_grade parameters family grade.val).trans (extendedSource_at parameters family grade)

theorem stateToCompatible_surjective (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : Function.Surjective (stateToCompatible parameters parameter inside) :=
  fun family => ⟨reconstructedConstrainedState parameters parameter inside family,
    stateToCompatible_reconstructed parameters parameter inside family⟩

theorem sourceToCompatible_surjective (parameters : PhaseParameters) : Function.Surjective (sourceToCompatible parameters) :=
  fun family => ⟨reconstructedConstrainedSource parameters family, sourceToCompatible_reconstructed parameters family⟩

/-- The exact original smooth real constrained state core is the actual
compatible dependent limit, not a family of unrelated representatives. -/
def stateCompatibleEquiv (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    stateSmoothRange parameters parameter inside ≃ₗ[ℝ] CompatibleStates parameters parameter inside :=
  LinearEquiv.ofBijective (stateToCompatible parameters parameter inside)
    ⟨stateToCompatible_injective parameters parameter inside, stateToCompatible_surjective parameters parameter inside⟩

def sourceCompatibleEquiv (parameters : PhaseParameters) :
    sourceSmoothRange parameters ≃ₗ[ℝ] CompatibleSources parameters :=
  LinearEquiv.ofBijective (sourceToCompatible parameters)
    ⟨sourceToCompatible_injective parameters, sourceToCompatible_surjective parameters⟩

theorem stateCompatibleEquiv_component (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : stateSmoothRange parameters parameter inside)
    (grade : AdmissibleGrade) :
    (stateCompatibleEquiv parameters parameter inside field).val grade =
      stateSmoothEmbedding parameters parameter inside grade.val grade.property field := rfl

theorem sourceCompatibleEquiv_component (parameters : PhaseParameters)
    (field : sourceSmoothRange parameters) (grade : AdmissibleGrade) :
    (sourceCompatibleEquiv parameters field).val grade =
      sourceSmoothEmbedding parameters grade.val grade.property field := rfl

theorem stateCompatibleEquiv_inverse_allGrades (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) (grade : ℕ) :
    stateToGrade parameters grade ((stateCompatibleEquiv parameters parameter inside).symm family).val =
      extendedState parameters parameter inside family grade := by
  have equality : stateToCompatible parameters parameter inside
      ((stateCompatibleEquiv parameters parameter inside).symm family) = family :=
    (stateCompatibleEquiv parameters parameter inside).apply_symm_apply family
  have core := extendedState_core parameters parameter inside
    ((stateCompatibleEquiv parameters parameter inside).symm family) grade
  rw [equality] at core
  exact core.symm

theorem sourceCompatibleEquiv_inverse_allGrades (parameters : PhaseParameters)
    (family : CompatibleSources parameters) (grade : ℕ) :
    quotientEta parameters grade ((sourceCompatibleEquiv parameters).symm family).val =
      extendedSource parameters family grade := by
  have equality : sourceToCompatible parameters ((sourceCompatibleEquiv parameters).symm family) = family :=
    (sourceCompatibleEquiv parameters).apply_symm_apply family
  have core := extendedSource_core parameters ((sourceCompatibleEquiv parameters).symm family) grade
  rw [equality] at core
  exact core.symm

end Grad.ConstrainedGrades
