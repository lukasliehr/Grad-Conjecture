import QV8Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter
open scoped Topology

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)
    (sequence : ℕ → stateSmoothRange parameters reference inside)
    (converges : ∀ grade : AdmissibleGrade,
      ∃ limit : stateRange parameters reference inside grade.val grade.property,
        Tendsto (fun index => stateSmoothEmbedding parameters reference inside
          grade.val grade.property (sequence index)) atTop (𝓝 limit))

/-- The same sequence forces compatibility of its completed-grade limits. -/
def convergentStateLimitFamily : CompatibleStates parameters reference inside :=
  ⟨fun grade => Classical.choose (converges grade), by
    intro lower upper ordered
    have lowered := ((stateLowering parameters reference inside lower.property ordered).continuous.tendsto
      (Classical.choose (converges upper))).comp (Classical.choose_spec (converges upper))
    simp only [Function.comp_def, stateLowering_core] at lowered
    exact tendsto_nhds_unique lowered (Classical.choose_spec (converges lower))⟩

/-- One actual original-width smooth real constrained core realizes every
completed limit, using the accepted COR26 reconstruction unchanged. -/
def convergentStateLimit : stateSmoothRange parameters reference inside :=
  (stateCompatibleEquiv parameters reference inside).symm
    (convergentStateLimitFamily parameters reference inside sequence converges)

theorem convergentStateLimit_grade (grade : AdmissibleGrade) :
    stateSmoothEmbedding parameters reference inside grade.val grade.property
      (convergentStateLimit parameters reference inside sequence converges) =
        Classical.choose (converges grade) := by
  exact congrArg (fun family : CompatibleStates parameters reference inside => family.val grade)
    ((stateCompatibleEquiv parameters reference inside).apply_symm_apply
      (convergentStateLimitFamily parameters reference inside sequence converges))

theorem convergentStateLimit_tendsto (grade : AdmissibleGrade) :
    Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
      (sequence index)) atTop (𝓝 (stateSmoothEmbedding parameters reference inside grade.val grade.property
        (convergentStateLimit parameters reference inside sequence converges))) := by
  rw [convergentStateLimit_grade]
  exact Classical.choose_spec (converges grade)

theorem convergentStateLimit_norm_le (grade : AdmissibleGrade) (bound : ℝ)
    (bounded : ∀ index, ‖stateSmoothEmbedding parameters reference inside grade.val grade.property
      (sequence index)‖ ≤ bound) :
    ‖stateSmoothEmbedding parameters reference inside grade.val grade.property
      (convergentStateLimit parameters reference inside sequence converges)‖ ≤ bound := by
  exact le_of_tendsto (convergentStateLimit_tendsto parameters reference inside sequence converges grade).norm
    (Filter.Eventually.of_forall bounded)

theorem convergentStateLimit_unique (candidate : stateSmoothRange parameters reference inside)
    (same : ∀ grade : AdmissibleGrade,
      Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
        (sequence index)) atTop (𝓝 (stateSmoothEmbedding parameters reference inside grade.val grade.property candidate))) :
    candidate = convergentStateLimit parameters reference inside sequence converges := by
  apply stateSmoothEmbedding_injective parameters reference inside 3 (le_refl 3)
  exact tendsto_nhds_unique (same ⟨3, le_refl 3⟩)
    (convergentStateLimit_tendsto parameters reference inside sequence converges ⟨3, le_refl 3⟩)

end Grad.NashMoser.OriginalLimit
