import BanachCalcSeriesInterface
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Convex.PathConnected

/-!
# Proofs of the NG_F04 and NG_F05 goals

Route (pinned Mathlib, documented in `BANACHCALC_HANDOFF.md`):

* the `j`-th derivative of a `C^∞` coefficient on the open set `U` has the
  Fréchet derivative `(iteratedFDeriv ℝ (j+1) f x).curryLeft` at every `x ∈ U`
  (`ContDiffAt.differentiableAt_iteratedFDeriv`, `fderiv_iteratedFDeriv`);
* NG_F04: `Summable.of_norm_bounded`, `continuousOn_tsum` (locally, then the
  closed ball is a neighborhood), `tendstoUniformlyOn_tsum_nat`;
* NG_F05: `hasFDerivAt_tsum_of_isPreconnected` on the open ball around `x`
  (convex, hence preconnected), with the derivative bound transported through
  the isometry `continuousMultilinearCurryLeftEquiv` (= `curryLeft`), and the
  limit derivative identified with `(operatorSeriesSum F (j+1) x).curryLeft`
  by `ContinuousLinearEquiv.map_tsum`.
-/

universe u v

open scoped ContDiff

namespace Grad.FiniteBanachCalculus

section Helpers

variable {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A natural number is below `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`. -/
theorem natCast_lt_infty (m : ℕ) : (m : ℕ∞ω) < ∞ :=
  WithTop.coe_lt_coe.2 (WithTop.coe_lt_top m)

/-- The first-direction insertion is an isometry of operator norms. -/
theorem norm_curryLeft (j : ℕ) (G : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) Y) :
    ‖G.curryLeft‖ = ‖G‖ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => X) Y).norm_map G

/-- On an open set, the `j`-th derivative of a `C^∞` map has Fréchet derivative
the first-direction insertion of the `(j+1)`-st derivative. -/
theorem hasFDerivAt_iteratedFDeriv_of_contDiffOn {U : Set X} (hU : IsOpen U) {f : X → Y}
    (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) {x : X} (hx : x ∈ U) :
    HasFDerivAt (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ (j + 1) f x).curryLeft x := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv (natCast_lt_infty j)
  have h1 := hd.hasFDerivAt
  rw [fderiv_iteratedFDeriv] at h1
  exact h1

/-- The first-direction insertion commutes with the operator-series sum. -/
theorem curryLeft_tsum (j : ℕ) (G : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) Y) :
    (∑' p, G p).curryLeft = ∑' p, (G p).curryLeft :=
  ContinuousLinearEquiv.map_tsum
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => X) Y).toContinuousLinearEquiv

end Helpers

/-- NG_F04: the uniform derivative-series limit exists as stated. -/
theorem actualOperatorSeriesLimit : OperatorSeriesLimitGoal.{u, v} := by
  intro X Y _ _ _ _ _ _ U F hU hF hM j
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, _, M, hMs, hbound⟩ := hM x hx j
    exact Summable.of_norm_bounded hMs fun p => hbound p x (Metric.mem_closedBall_self hr.le)
  · intro x hx
    obtain ⟨r, hr, hball, M, hMs, hbound⟩ := hM x hx j
    have hcont : ∀ p, ContinuousOn (iteratedFDeriv ℝ j (F p)) (Metric.closedBall x r) :=
      fun p y hy =>
        (hasFDerivAt_iteratedFDeriv_of_contDiffOn hU (hF p) j (hball hy)).continuousAt.continuousWithinAt
    have hsum : ContinuousOn (fun y => ∑' p, iteratedFDeriv ℝ j (F p) y) (Metric.closedBall x r) :=
      continuousOn_tsum hcont hMs fun p y hy => hbound p y hy
    exact (hsum.continuousAt (Metric.closedBall_mem_nhds x hr)).continuousWithinAt
  · intro x hx
    obtain ⟨r, hr, hball, M, hMs, hbound⟩ := hM x hx j
    exact ⟨r, hr, hball, tendstoUniformlyOn_tsum_nat hMs fun p y hy => hbound p y hy⟩

/-- NG_F05: the operator-series sum has the stated Fréchet derivative. -/
theorem actualOperatorSeriesDerivative : OperatorSeriesDerivativeGoal.{u, v} := by
  intro X Y _ _ _ _ _ _ U F hU hF hM j x₀ hx₀
  obtain ⟨r₀, hr₀, _, M₀, hM₀, hbound₀⟩ := hM x₀ hx₀ j
  obtain ⟨r₁, hr₁, hball₁, M₁, hM₁, hbound₁⟩ := hM x₀ hx₀ (j + 1)
  have hsub : Metric.ball x₀ r₁ ⊆ U := Metric.ball_subset_closedBall.trans hball₁
  have key := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ)
    (f := fun p => iteratedFDeriv ℝ j (F p))
    (f' := fun p y => (iteratedFDeriv ℝ (j + 1) (F p) y).curryLeft)
    hM₁ Metric.isOpen_ball (convex_ball x₀ r₁).isPreconnected
    (fun p y hy => hasFDerivAt_iteratedFDeriv_of_contDiffOn hU (hF p) j (hsub hy))
    (fun p y hy => by
      show ‖(iteratedFDeriv ℝ (j + 1) (F p) y).curryLeft‖ ≤ M₁ p
      rw [norm_curryLeft]
      exact hbound₁ p y (Metric.ball_subset_closedBall hy))
    (Metric.mem_ball_self hr₁)
    (Summable.of_norm_bounded hM₀ fun p => hbound₀ p x₀ (Metric.mem_closedBall_self hr₀.le))
    (Metric.mem_ball_self hr₁)
  rw [← curryLeft_tsum] at key
  exact key

end Grad.FiniteBanachCalculus
