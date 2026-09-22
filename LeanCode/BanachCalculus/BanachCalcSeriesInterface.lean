import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Finite Banach calculus: the operator-series interface (NG_F04, NG_F05)

Group `finite_banach_calculus`, units NG_F04 (uniform derivative-series limit,
a construction) and NG_F05 (derivative of the operator-series sum, a lemma).

Data: Banach spaces `X`, `Y`; an open `U ⊆ X`; smooth coefficient maps
`F p : X → Y` (`ContDiffOn ℝ ∞ (F p) U`); and locally summable operator
majorants: for every `x ∈ U` and every order `j` some closed ball around `x`
inside `U` carries a summable `M : ℕ → ℝ` with `‖D^j F_p‖ ≤ M p` uniformly on
the ball (`HasLocalOperatorMajorants`). This is implied by the cards'
"every small convex closed ball in `U` and each finite `j` have summable
bounds", so the goals below are not narrowed.

* `operatorSeriesSum F j x = ∑' p, iteratedFDeriv ℝ j (F p) x` is the NG_F04
  construction `G_j = Σ_p D^j F_p`, valued in the complete `j`-multilinear
  operator target `ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Y`.
* `OperatorSeriesLimitGoal` (NG_F04): for every `j`, the series converges at
  every point of `U`, `G_j` is continuous on `U`, and the partial sums
  converge to `G_j` uniformly on a closed ball inside `U` around every point
  of `U` (the locally uniform continuous limit).
* `OperatorSeriesDerivativeGoal` (NG_F05): `G_j` has Fréchet derivative
  `h ↦ G_{j+1}(x)[h, ·]` (the first-direction insertion `curryLeft` of
  `G_{j+1} x`) at every `x ∈ U`.
-/

universe u v

open scoped ContDiff

namespace Grad.FiniteBanachCalculus

/-- NG_F04 construction: the operator-series sum at order `j`, the pointwise sum
of the `j`-th Fréchet derivatives of the coefficient maps in the complete
`j`-multilinear operator target. -/
noncomputable def operatorSeriesSum {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : ℕ → X → Y) (j : ℕ) (x : X) : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Y :=
  ∑' p, iteratedFDeriv ℝ j (F p) x

/-- Locally summable operator majorants (the NG_F04/NG_F05 input): for every
`x ∈ U` and every order `j`, some closed ball around `x` inside `U` carries a
summable majorant `M` with `‖iteratedFDeriv ℝ j (F p) y‖ ≤ M p` for all `p` and
all `y` in the ball. -/
def HasLocalOperatorMajorants {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (F : ℕ → X → Y) : Prop :=
  ∀ x ∈ U, ∀ j : ℕ, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
    ∃ M : ℕ → ℝ, Summable M ∧
      ∀ p : ℕ, ∀ y ∈ Metric.closedBall x r, ‖iteratedFDeriv ℝ j (F p) y‖ ≤ M p

/-- NG_F04 (uniform derivative-series limit). For Banach `X`, `Y`, open `U`,
smooth coefficients with locally summable operator majorants, and every order
`j`: the derivative series is summable at every point of `U`, its sum
`operatorSeriesSum F j` is continuous on `U`, and around every point of `U`
there is a closed ball inside `U` on which the partial sums converge
uniformly to the sum. -/
def OperatorSeriesLimitGoal : Prop :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (U : Set X) (F : ℕ → X → Y),
    IsOpen U → (∀ p, ContDiffOn ℝ ∞ (F p) U) → HasLocalOperatorMajorants U F →
    ∀ j : ℕ,
      (∀ x ∈ U, Summable fun p => iteratedFDeriv ℝ j (F p) x) ∧
      ContinuousOn (operatorSeriesSum F j) U ∧
      ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
        TendstoUniformlyOn (fun N y => ∑ p ∈ Finset.range N, iteratedFDeriv ℝ j (F p) y)
          (operatorSeriesSum F j) Filter.atTop (Metric.closedBall x r)

/-- NG_F05 (derivative of the operator-series sum). Under the same data, for
every order `j` and every `x ∈ U`, `operatorSeriesSum F j` has the Fréchet
derivative `(operatorSeriesSum F (j + 1) x).curryLeft`, i.e.
`h ↦ G_{j+1}(x)[h, ·]`, at `x`. -/
def OperatorSeriesDerivativeGoal : Prop :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (U : Set X) (F : ℕ → X → Y),
    IsOpen U → (∀ p, ContDiffOn ℝ ∞ (F p) U) → HasLocalOperatorMajorants U F →
    ∀ j : ℕ, ∀ x ∈ U,
      HasFDerivAt (operatorSeriesSum F j) (operatorSeriesSum F (j + 1) x).curryLeft x

end Grad.FiniteBanachCalculus
