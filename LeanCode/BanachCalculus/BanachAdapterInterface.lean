import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Finite Banach calculus: the conditional finite-loss completion adapter (NG_F07)

Group `finite_banach_calculus`, unit NG_F07 (kind assembly; source atom
R6:generic-completion; NM(11)/NM03 Banach-realization paragraph of the
Nash–Moser blueprint; reviewer completion in NONLINEAR_REVIEW §4.8 with input
grade `t = s + R_(m+1)`).

The unit is a GENERIC theorem over abstract Banach scales.  Nothing is
narrowed to a project carrier and no project inverse is assumed: every
analytic input of R6 is modeled as explicit data below.

## Data (one fixed target grade `s`, one fixed source/state grade `t`)

* `X`: the completed state space at grade `t` (Banach); `O : Set X` the open
  state domain ("the grade-`t` low ball"); `C : Submodule ℝ X` the dense smooth
  state core.
* `F`: the completed source space at grade `t` (Banach); `CF : Submodule ℝ F`
  the dense smooth source core.
* `E`: the target space `E_s` (Banach).
* `V : C → CF →ₗ[ℝ] E`: the supplied core family `b ↦ (f ↦ V_b f)`, linear
  in the core source.
* `D : (j : ℕ) → C → MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E)`: the
  core directional derivatives `D^j V_b [h_1, …, h_j] f`, multilinear in the
  core directions and linear in the core source, `D 0 = V`.

## Hypotheses (R6 / NM(11) modeled as data)

* density of both cores, openness of `O`;
* `D 0 b h = V b` (order zero is the family itself);
* the NM(11)-type one-high estimate at the input grade `t = s + R_(m+1)`, in
  the form actually consumed by the completion: for every order `j ≤ m + 1`
  and every `b₀ ∈ O` some ball around `b₀` carries a constant `K` with
  `‖D^j V_b [h] f‖ ≤ K * ∏ i, ‖h i‖ * ‖f‖` on core states `b ∈ O` of the ball
  and all core directions/sources.  NM(11) at grade `t` implies this: its
  right side is dominated by `C_j [(1 + ‖b‖_t) + 1 + j] ‖ι₀‖^{j+1} ∏‖h_i‖_t ‖f‖_t`
  on a ball, since every grade-`0` norm is bounded by the grade-`t` norm
  through the continuous grade inclusion `ι₀` and the state norm is bounded on
  the ball (this is exactly "each derivative through `m` is locally Lipschitz
  in the grade-`t` variables on bounded sets");
* continuity of every core derivative `D^j V_b [h] f` (`j ≤ m + 1`) in the
  core state `b ∈ O` for fixed core directions and source (implied by the
  joint continuity of NM03);
* the actual core directional derivatives: for `j ≤ m`, along every core
  direction `h`, at every core point `b + τ • h ∈ O`, the map
  `σ ↦ D^j V_{b + σ h} [h'] f` has derivative `D^{j+1} V_{b + τ h} [h, h'] f`
  (new direction in the first slot, Mathlib's `curryLeft` convention).

## Output

`BanachCompletionAdapterGoal`: (existence) a map `W : X → (F →L[ℝ] E)` that is
`C^m` on `O` in Mathlib's Fréchet sense (`ContDiffOn ℝ m W O`), agrees with the
core family on core points, whose `j`-th Fréchet derivatives at core points
are the completed multilinear extensions of the core derivatives for all
`j ≤ m` (with the completed operator norms bounded by every core constant), and
which is the unique continuous map on `O` agreeing with the family on core
points; (lifts) any two such realizations at a common pair of grades related by
continuous linear grade inclusions agree on the image of the higher grade.

Proofs: `BanachAdapterProof` (and its helper modules); goal-only consumers:
`BanachAdapterConsumer`.
-/

universe u v w

namespace Grad.FiniteBanachCalculus

/-- NG_F07, existence and uniqueness part.  See the module docstring for the
meaning of every datum.  The order `m` is a natural number; core derivatives
are supplied through order `m + 1` (the fixed finite loss `R_(m+1)` is absorbed
in the choice of the input grade `t` of the spaces `X`, `F`). -/
def BanachCompletionAdapterExistsGoal : Prop :=
  ∀ {X : Type u} {F : Type v} {E : Type w}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (C : Submodule ℝ X) (CF : Submodule ℝ F) (O : Set X)
    (V : C → CF →ₗ[ℝ] E)
    (D : (j : ℕ) → C → MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E)),
    Dense (C : Set X) → Dense (CF : Set F) → IsOpen O →
    (∀ (b : C) (h : Fin 0 → C), D 0 b h = V b) →
    (∀ j ≤ m + 1, ∀ b₀ ∈ O, ∃ r > 0, ∃ K : ℝ,
        ∀ (b : C), (b : X) ∈ O → dist (b : X) b₀ < r →
          ∀ (h : Fin j → C) (f : CF), ‖D j b h f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) →
    (∀ j ≤ m + 1, ∀ (h : Fin j → C) (f : CF),
        ContinuousOn (fun b : C => D j b h f) {b : C | (b : X) ∈ O}) →
    (∀ j ≤ m, ∀ (b h : C) (h' : Fin j → C) (f : CF) (τ : ℝ),
        ((b + τ • h : C) : X) ∈ O →
          HasDerivAt (fun σ : ℝ => D j (b + σ • h) h' f)
            (D (j + 1) (b + τ • h) (Fin.cons h h') f) τ) →
    ∃ W : X → F →L[ℝ] E,
      ContDiffOn ℝ m W O ∧
      (∀ (b : C), (b : X) ∈ O → ∀ f : CF, W b f = V b f) ∧
      (∀ j ≤ m, ∀ (b : C), (b : X) ∈ O → ∀ (h : Fin j → C) (f : CF),
          iteratedFDeriv ℝ j W b (fun i => (h i : X)) f = D j b h f) ∧
      (∀ j ≤ m, ∀ (b : C), (b : X) ∈ O → ∀ K : ℝ, 0 ≤ K →
          (∀ (h : Fin j → C) (f : CF), ‖D j b h f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) →
          ‖iteratedFDeriv ℝ j W b‖ ≤ K) ∧
      (∀ W' : X → F →L[ℝ] E, ContinuousOn W' O →
          (∀ (b : C), (b : X) ∈ O → ∀ f : CF, W' b f = V b f) → Set.EqOn W' W O)

/-- NG_F07, compatibility under common higher-grade lifts.  Two grades `t' ≥ t`
of the same scale are related by continuous linear grade inclusions
`ιX : X' →L[ℝ] X` (states) and `ιF : F' →L[ℝ] F` (sources) mapping cores into
cores and the higher domain `O'` into `O`, and the core family at the higher
grade is the restriction of the core family at the lower grade.  Then any
continuous realization `W` on `O` of the lower family and any continuous
realization `W'` on `O'` of the higher family (each agreeing with its family
on core points; the higher cores dense, `O'` open) satisfy
`W' x f = W (ιX x) (ιF f)` on the image of the higher grade. -/
def BanachCompletionAdapterLiftGoal : Prop :=
  ∀ {X : Type u} {F : Type v} {E : Type w} {X' : Type u} {F' : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [CompleteSpace X']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    (C : Submodule ℝ X) (CF : Submodule ℝ F) (O : Set X) (V : C → CF →ₗ[ℝ] E)
    (C' : Submodule ℝ X') (CF' : Submodule ℝ F') (O' : Set X') (V' : C' → CF' →ₗ[ℝ] E)
    (ιX : X' →L[ℝ] X) (ιF : F' →L[ℝ] F)
    (hιC : ∀ c : C', ιX c ∈ C) (hιCF : ∀ f : CF', ιF f ∈ CF),
    Dense (C' : Set X') → Dense (CF' : Set F') → IsOpen O' →
    (∀ x ∈ O', ιX x ∈ O) →
    (∀ (b : C') (f : CF'), V' b f = V ⟨ιX b, hιC b⟩ ⟨ιF f, hιCF f⟩) →
    ∀ (W : X → F →L[ℝ] E) (W' : X' → F' →L[ℝ] E),
      ContinuousOn W O → (∀ (b : C), (b : X) ∈ O → ∀ f : CF, W b f = V b f) →
      ContinuousOn W' O' → (∀ (b : C'), (b : X') ∈ O' → ∀ f : CF', W' b f = V' b f) →
      ∀ x ∈ O', ∀ f : F', W' x f = W (ιX x) (ιF f)

/-- NG_F07 (conditional finite-loss Banach completion adapter): the unique
local `C^m` realization `O_t → L(F_t, E_s)` of a core family with actual
jointly continuous core derivatives through order `m + 1` obeying the
NM(11)-type one-high estimates at the input grade `t = s + R_(m+1)`, agreeing
with the family on core points, with completed derivatives, and compatible
under common higher-grade lifts. -/
def BanachCompletionAdapterGoal : Prop :=
  BanachCompletionAdapterExistsGoal.{u, v, w} ∧ BanachCompletionAdapterLiftGoal.{u, v, w}

end Grad.FiniteBanachCalculus
