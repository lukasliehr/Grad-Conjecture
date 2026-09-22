import QU5Goal

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges

/-- The exact COR26 forward-family input: one literal constrained smooth
state simultaneously supplies every compatible finite grade q >= 3. -/
theorem smoothState_compatible_family (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : stateSmoothRange parameters parameter inside) :
    ∀ (lower upper : ℕ) (large : 3 ≤ lower) (ordered : lower ≤ upper),
      stateLowering parameters parameter inside large ordered
        (stateSmoothEmbedding parameters parameter inside upper (large.trans ordered) field) =
          stateSmoothEmbedding parameters parameter inside lower large field := by
  intro lower upper large ordered
  exact ((actualConstrainedInclusions parameters parameter inside).1 lower upper large ordered).2.2.2.2.2.2.1 field

theorem smoothSource_compatible_family (parameters : PhaseParameters)
    (field : sourceSmoothRange parameters) :
    ∀ (lower upper : ℕ) (large : 3 ≤ lower) (ordered : lower ≤ upper),
      sourceLowering parameters large ordered
        (sourceSmoothEmbedding parameters upper (large.trans ordered) field) =
          sourceSmoothEmbedding parameters lower large field := by
  intro lower upper large ordered
  exact sourceLowering_core parameters large ordered field

/-- Equality at a lower constrained grade detects equality of the actual
higher-grade objects; this uses completed coefficient injectivity. -/
theorem stateLowering_eq_iff {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (first second : stateRange parameters parameter inside upper (large.trans ordered)) :
    stateLowering parameters parameter inside large ordered first =
      stateLowering parameters parameter inside large ordered second ↔ first = second :=
  (stateLowering_injective parameters parameter inside large ordered).eq_iff

theorem sourceLowering_eq_iff {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (first second : sourceRange parameters upper (large.trans ordered)) :
    sourceLowering parameters large ordered first = sourceLowering parameters large ordered second ↔ first = second :=
  (sourceLowering_injective parameters large ordered).eq_iff

end Grad.ConstrainedGrades
