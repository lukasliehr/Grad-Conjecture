import QV6Topology

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.QuotientProjection

/-- COR26: the literal smooth real constrained cores are exactly the
compatible families in the actual grades q >= 3. One inverse realizes all
grades simultaneously, preserving the original norms and full seminorm topology. -/
def ConstrainedCompatibleLimitGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain),
    Function.Bijective (stateToCompatible parameters parameter inside) ∧
    Function.Bijective (sourceToCompatible parameters) ∧
    (∀ (field : stateSmoothRange parameters parameter inside) (grade : AdmissibleGrade),
      ‖(stateCompatibleEquiv parameters parameter inside field).val grade‖ =
        ‖stateToGrade parameters grade.val field.val‖) ∧
    (∀ (field : sourceSmoothRange parameters) (grade : AdmissibleGrade),
      ‖(sourceCompatibleEquiv parameters field).val grade‖ = quotientNorm parameters grade.val field.val) ∧
    (∀ (family : CompatibleStates parameters parameter inside) (grade : ℕ),
      stateToGrade parameters grade ((stateCompatibleEquiv parameters parameter inside).symm family).val =
        extendedState parameters parameter inside family grade) ∧
    (∀ (family : CompatibleSources parameters) (grade : ℕ),
      quotientEta parameters grade ((sourceCompatibleEquiv parameters).symm family).val =
        extendedSource parameters family grade) ∧
    stateOriginalTopology parameters parameter inside =
      TopologicalSpace.induced (stateToCompatible parameters parameter inside) inferInstance ∧
    sourceOriginalTopology parameters = TopologicalSpace.induced (sourceToCompatible parameters) inferInstance

theorem actualConstrainedCompatibleLimit : ConstrainedCompatibleLimitGoal := by
  intro parameters parameter inside
  exact ⟨⟨stateToCompatible_injective parameters parameter inside, stateToCompatible_surjective parameters parameter inside⟩,
    ⟨sourceToCompatible_injective parameters, sourceToCompatible_surjective parameters⟩,
    stateCompatibleEquiv_original_norm parameters parameter inside,
    sourceCompatibleEquiv_original_norm parameters,
    stateCompatibleEquiv_inverse_allGrades parameters parameter inside,
    sourceCompatibleEquiv_inverse_allGrades parameters,
    stateOriginalTopology_eq_induced parameters parameter inside, sourceOriginalTopology_eq_induced parameters⟩

end Grad.ConstrainedGrades
