import QU4ConstrainedInclusions

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges

/-- COR25 on the actual constrained scales: the maps are induced by the
literal ambient coefficient inclusions and have constant exactly one. -/
def ConstrainedInclusionGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain),
    (∀ (lower upper : ℕ) (large : 3 ≤ lower) (ordered : lower ≤ upper),
      ‖stateLowering parameters parameter inside large ordered‖ ≤ 1 ∧
      ‖sourceLowering parameters large ordered‖ ≤ 1 ∧
      Function.Injective (stateLowering parameters parameter inside large ordered) ∧
      Function.Injective (sourceLowering parameters large ordered) ∧
      (∀ field, (stateLowering parameters parameter inside large ordered field).val =
        xLowering parameters ordered field.val) ∧
      (∀ field, (sourceLowering parameters large ordered field).val = zLowering parameters ordered field.val) ∧
      (∀ field : stateSmoothRange parameters parameter inside,
        stateLowering parameters parameter inside large ordered
          (stateSmoothEmbedding parameters parameter inside upper (large.trans ordered) field) =
            stateSmoothEmbedding parameters parameter inside lower large field) ∧
      (∀ field : sourceSmoothRange parameters,
        sourceLowering parameters large ordered (sourceSmoothEmbedding parameters upper (large.trans ordered) field) =
          sourceSmoothEmbedding parameters lower large field)) ∧
    (∀ (grade : ℕ) (large : 3 ≤ grade),
      (∀ field, stateLowering parameters parameter inside large (le_refl grade) field = field) ∧
      (∀ field, sourceLowering parameters large (le_refl grade) field = field)) ∧
    (∀ (lower middle upper : ℕ) (large : 3 ≤ lower) (first : lower ≤ middle) (second : middle ≤ upper),
      (∀ field, stateLowering parameters parameter inside large first
        (stateLowering parameters parameter inside (large.trans first) second field) =
          stateLowering parameters parameter inside large (first.trans second) field) ∧
      (∀ field, sourceLowering parameters large first (sourceLowering parameters (large.trans first) second field) =
        sourceLowering parameters large (first.trans second) field))

theorem actualConstrainedInclusions : ConstrainedInclusionGoal := by
  intro parameters parameter inside
  refine ⟨?_, ?_, ?_⟩
  · intro lower upper large ordered
    exact ⟨stateLowering_opNorm_le_one parameters parameter inside large ordered,
      sourceLowering_opNorm_le_one parameters large ordered,
      stateLowering_injective parameters parameter inside large ordered,
      sourceLowering_injective parameters large ordered,
      stateLowering_coe parameters parameter inside large ordered,
      sourceLowering_coe parameters large ordered,
      stateLowering_core parameters parameter inside large ordered,
      sourceLowering_core parameters large ordered⟩
  · intro grade large
    exact ⟨stateLowering_self parameters parameter inside grade large, sourceLowering_self parameters grade large⟩
  · intro lower middle upper large first second
    exact ⟨stateLowering_trans parameters parameter inside large first second,
      sourceLowering_trans parameters large first second⟩

end Grad.ConstrainedGrades
