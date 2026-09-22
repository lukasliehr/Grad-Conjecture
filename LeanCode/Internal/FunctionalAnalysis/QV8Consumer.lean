import QV7Goal

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.QuotientProjection

/-- A universal simultaneous representative, not one choice inside the
grade quantifier. The representative is literally smooth, real and constrained. -/
theorem compatibleState_has_unique_smooth_representative (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    ∃! field : stateSmoothRange parameters parameter inside,
      ∀ grade : AdmissibleGrade,
        stateSmoothEmbedding parameters parameter inside grade.val grade.property field = family.val grade := by
  obtain ⟨field, equality⟩ := (actualConstrainedCompatibleLimit parameters parameter inside).1.2 family
  have represents : ∀ grade : AdmissibleGrade,
      stateSmoothEmbedding parameters parameter inside grade.val grade.property field = family.val grade :=
    fun grade => congrArg (fun values : CompatibleStates parameters parameter inside => values.val grade) equality
  refine ⟨field, represents, ?_⟩
  intro other otherRepresents
  apply stateSmoothEmbedding_injective parameters parameter inside 3 (le_refl 3)
  exact (otherRepresents ⟨3, le_refl 3⟩).trans (represents ⟨3, le_refl 3⟩).symm

theorem compatibleSource_has_unique_smooth_representative (parameters : PhaseParameters)
    (family : CompatibleSources parameters) :
    ∃! field : sourceSmoothRange parameters,
      ∀ grade : AdmissibleGrade, sourceSmoothEmbedding parameters grade.val grade.property field = family.val grade := by
  obtain ⟨field, equality⟩ := sourceToCompatible_surjective parameters family
  have represents : ∀ grade : AdmissibleGrade,
      sourceSmoothEmbedding parameters grade.val grade.property field = family.val grade :=
    fun grade => congrArg (fun values : CompatibleSources parameters => values.val grade) equality
  refine ⟨field, represents, ?_⟩
  intro other otherRepresents
  apply sourceSmoothEmbedding_injective parameters 3 (le_refl 3)
  exact (otherRepresents ⟨3, le_refl 3⟩).trans (represents ⟨3, le_refl 3⟩).symm

/-- All original norms of the one reconstructed state are the actual
coordinates of the uniquely extended family, including omitted low grades. -/
theorem reconstructedState_original_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) (grade : ℕ) :
    stateOriginalSeminorms parameters parameter inside grade
      ((stateCompatibleEquiv parameters parameter inside).symm family) =
        ‖extendedState parameters parameter inside family grade‖ := by
  rw [stateOriginalSeminorms_apply, stateCompatibleEquiv_inverse_allGrades]

theorem reconstructedSource_original_norm (parameters : PhaseParameters)
    (family : CompatibleSources parameters) (grade : ℕ) :
    sourceOriginalSeminorms parameters grade ((sourceCompatibleEquiv parameters).symm family) =
      ‖extendedSource parameters family grade‖ := by
  change ‖quotientEta parameters grade ((sourceCompatibleEquiv parameters).symm family).val‖ = _
  rw [sourceCompatibleEquiv_inverse_allGrades]

end Grad.ConstrainedGrades
