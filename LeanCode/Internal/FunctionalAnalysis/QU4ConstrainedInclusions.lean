import QU3AmbientCompatibility

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.AxisCore Grad.SmoothingFamily Grad.Constraints
open Grad.RealFixedRanges Grad.CompletedReality Grad.QuotientProjection

theorem xLowering_mem {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateRange parameters parameter inside upper (large.trans ordered)) :
    xLowering parameters ordered field.val ∈ stateRange parameters parameter inside lower large := by
  have member := (mem_stateRange parameters parameter inside upper (large.trans ordered) field.val).1 field.property
  rw [mem_stateRange, ← xLowering_projection, ← xLowering_conjugation, member.1, member.2]
  exact ⟨rfl, rfl⟩

theorem zLowering_mem {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : sourceRange parameters upper (large.trans ordered)) :
    zLowering parameters ordered field.val ∈ sourceRange parameters lower large := by
  have member := (mem_sourceRange parameters upper (large.trans ordered) field.val).1 field.property
  rw [mem_sourceRange, ← zLowering_projection, ← zLowering_conjugation, member.1, member.2]
  exact ⟨rfl, rfl⟩

/-- The canonical real constrained inclusion induced by the actual ambient
coefficient inclusion. No representative choice or ambient retraction is used. -/
def stateLowering {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    stateRange parameters parameter inside upper (large.trans ordered) →L[ℝ]
      stateRange parameters parameter inside lower large :=
  (((xLowering parameters ordered).restrictScalars ℝ).comp
    (stateRange parameters parameter inside upper (large.trans ordered)).subtypeL).codRestrict
      (stateRange parameters parameter inside lower large) (xLowering_mem parameters parameter inside large ordered)

def sourceLowering {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    sourceRange parameters upper (large.trans ordered) →L[ℝ] sourceRange parameters lower large :=
  (((zLowering parameters ordered).restrictScalars ℝ).comp
    (sourceRange parameters upper (large.trans ordered)).subtypeL).codRestrict
      (sourceRange parameters lower large) (zLowering_mem parameters large ordered)

theorem stateLowering_coe {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateRange parameters parameter inside upper (large.trans ordered)) :
    (stateLowering parameters parameter inside large ordered field).val = xLowering parameters ordered field.val := rfl

theorem sourceLowering_coe {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : sourceRange parameters upper (large.trans ordered)) :
    (sourceLowering parameters large ordered field).val = zLowering parameters ordered field.val := rfl

theorem stateLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateRange parameters parameter inside upper (large.trans ordered)) :
    ‖stateLowering parameters parameter inside large ordered field‖ ≤ ‖field‖ := by
  change ‖xLowering parameters ordered field.val‖ ≤ ‖field.val‖
  exact xLowering_norm_le parameters ordered field.val

theorem sourceLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : sourceRange parameters upper (large.trans ordered)) :
    ‖sourceLowering parameters large ordered field‖ ≤ ‖field‖ := by
  change ‖zLowering parameters ordered field.val‖ ≤ ‖field.val‖
  exact zLowering_norm_le parameters ordered field.val

theorem stateLowering_opNorm_le_one {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    ‖stateLowering parameters parameter inside large ordered‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using stateLowering_norm_le parameters parameter inside large ordered field

theorem sourceLowering_opNorm_le_one {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) : ‖sourceLowering parameters large ordered‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using sourceLowering_norm_le parameters large ordered field

theorem stateLowering_injective {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    Function.Injective (stateLowering parameters parameter inside large ordered) := by
  intro first second equality
  exact Subtype.ext (xLowering_injective parameters ordered (congrArg Subtype.val equality))

theorem sourceLowering_injective {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) : Function.Injective (sourceLowering parameters large ordered) := by
  intro first second equality
  exact Subtype.ext (zLowering_injective parameters ordered (congrArg Subtype.val equality))

theorem stateLowering_core {lower upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (field : stateSmoothRange parameters parameter inside) :
    stateLowering parameters parameter inside large ordered
      (stateSmoothEmbedding parameters parameter inside upper (large.trans ordered) field) =
        stateSmoothEmbedding parameters parameter inside lower large field :=
  Subtype.ext (xLowering_core parameters ordered field.val)

theorem sourceLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (field : sourceSmoothRange parameters) :
    sourceLowering parameters large ordered (sourceSmoothEmbedding parameters upper (large.trans ordered) field) =
      sourceSmoothEmbedding parameters lower large field := Subtype.ext (zLowering_core parameters ordered field.val)

theorem stateLowering_self (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateRange parameters parameter inside grade large) :
    stateLowering parameters parameter inside large (le_refl grade) field = field :=
  Subtype.ext (xLowering_self parameters grade field.val)

theorem sourceLowering_self (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : sourceRange parameters grade large) :
    sourceLowering parameters large (le_refl grade) field = field := Subtype.ext (zLowering_self parameters grade field.val)

theorem stateLowering_trans {lower middle upper : ℕ} (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (large : 3 ≤ lower)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (field : stateRange parameters parameter inside upper ((large.trans first).trans second)) :
    stateLowering parameters parameter inside large first
      (stateLowering parameters parameter inside (large.trans first) second field) =
        stateLowering parameters parameter inside large (first.trans second) field :=
  Subtype.ext (xLowering_trans parameters first second field.val)

theorem sourceLowering_trans {lower middle upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : sourceRange parameters upper ((large.trans first).trans second)) :
    sourceLowering parameters large first (sourceLowering parameters (large.trans first) second field) =
      sourceLowering parameters large (first.trans second) field :=
  Subtype.ext (zLowering_trans parameters first second field.val)

end Grad.ConstrainedGrades
