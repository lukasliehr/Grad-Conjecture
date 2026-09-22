import QS2ClosedRanges

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.RealFixedRanges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisCore
open Grad.SmoothingFamily Grad.Cor18 Grad.QuotientProjection Grad.CompletedReality

/-- Identical smooth equations; no normed-space instance on the all-grade core. -/
def stateSmoothRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : Submodule ℝ (StateCore parameters) :=
  ((fullProjection parameters parameter inside).restrictScalars ℝ - LinearMap.id).ker ⊓
    (xCoreConjugation parameters - LinearMap.id).ker

def sourceSmoothRange (parameters : PhaseParameters) : Submodule ℝ (SmoothQuotient parameters) :=
  ((quotientProjection parameters).restrictScalars ℝ - LinearMap.id).ker ⊓
    (zCoreConjugation parameters - LinearMap.id).ker

theorem mem_stateSmoothRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : StateCore parameters) :
    field ∈ stateSmoothRange parameters parameter inside ↔
      fullProjection parameters parameter inside field = field ∧
      xCoreConjugation parameters field = field := by
  simp only [stateSmoothRange, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.restrictScalars_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_sourceSmoothRange (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    field ∈ sourceSmoothRange parameters ↔ quotientProjection parameters field = field ∧
      zCoreConjugation parameters field = field := by
  simp only [sourceSmoothRange, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.restrictScalars_apply, LinearMap.id_apply, sub_eq_zero]

theorem stateToGrade_mem_iff (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateCore parameters) :
    stateToGrade parameters grade field ∈ stateRange parameters parameter inside grade large ↔
      field ∈ stateSmoothRange parameters parameter inside := by
  rw [mem_stateRange, stateProjection_core, xConjugation_eta, mem_stateSmoothRange]
  exact and_congr (stateToGrade_injective parameters grade).eq_iff
    (stateToGrade_injective parameters grade).eq_iff

theorem quotientEta_mem_iff (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : SmoothQuotient parameters) :
    quotientEta parameters grade field ∈ sourceRange parameters grade large ↔
      field ∈ sourceSmoothRange parameters := by
  rw [mem_sourceRange, sourceProjection_core, mem_sourceSmoothRange]
  have conjugate : zConjugation parameters grade (quotientEta parameters grade field) =
      quotientEta parameters grade (zCoreConjugation parameters field) :=
    zConjugation_eta parameters grade field
  rw [conjugate]
  exact and_congr (quotientEta_injective parameters grade).eq_iff
    (quotientEta_injective parameters grade).eq_iff

def stateSmoothEmbedding (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateSmoothRange parameters parameter inside →ₗ[ℝ]
      stateRange parameters parameter inside grade large where
  toFun field := ⟨stateToGrade parameters grade field.val,
    (stateToGrade_mem_iff parameters parameter inside grade large field.val).2 field.property⟩
  map_add' first second := by
    apply Subtype.ext
    exact (stateToGrade parameters grade).map_add first.val second.val
  map_smul' scalar field := by
    apply Subtype.ext
    exact ((stateToGrade parameters grade).restrictScalars ℝ).map_smul scalar field.val

def sourceSmoothEmbedding (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    sourceSmoothRange parameters →ₗ[ℝ] sourceRange parameters grade large where
  toFun field := ⟨quotientEta parameters grade field.val,
    (quotientEta_mem_iff parameters grade large field.val).2 field.property⟩
  map_add' first second := by
    apply Subtype.ext
    exact (quotientEta parameters grade).map_add first.val second.val
  map_smul' scalar field := by
    apply Subtype.ext
    exact ((quotientEta parameters grade).restrictScalars ℝ).map_smul scalar field.val

theorem stateSmoothEmbedding_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters parameter inside) :
    ‖stateSmoothEmbedding parameters parameter inside grade large field‖ =
      ‖stateToGrade parameters grade field.val‖ := rfl

theorem sourceSmoothEmbedding_norm (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : sourceSmoothRange parameters) :
    ‖sourceSmoothEmbedding parameters grade large field‖ = quotientNorm parameters grade field.val := rfl

theorem stateSmoothEmbedding_injective (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Function.Injective (stateSmoothEmbedding parameters parameter inside grade large) := by
  intro first second equality
  exact Subtype.ext ((stateToGrade_injective parameters grade) (congrArg Subtype.val equality))

theorem sourceSmoothEmbedding_injective (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    Function.Injective (sourceSmoothEmbedding parameters grade large) := by
  intro first second equality
  exact Subtype.ext ((quotientEta_injective parameters grade) (congrArg Subtype.val equality))

end Grad.RealFixedRanges
