import AKM2CountableHilbertWeakExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion

theorem WeakConverges.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {sequence : ℕ → E} {limit : E} (convergence : WeakConverges sequence limit)
    (mapping : E →L[ℝ] F) : WeakConverges (mapping ∘ sequence) (mapping limit) :=
  fun test => convergence (test.comp mapping)

theorem WeakConverges.unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {sequence : ℕ → H} {first second : H}
    (one : WeakConverges sequence first) (two : WeakConverges sequence second) : first = second := by
  apply ext_inner_left ℝ
  intro test
  exact tendsto_nhds_unique (one (InnerProductSpace.toDual ℝ H test))
    (two (InnerProductSpace.toDual ℝ H test))

theorem WeakConverges.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {sequence other : ℕ → E} {limit : E}
    (convergence : WeakConverges sequence limit) (same : sequence =ᶠ[atTop] other) :
    WeakConverges other limit := by
  intro test
  exact (convergence test).congr' (same.mono (fun _ h => congrArg test h))

/-- Eventual restriction or grade-comparison identities pass to the SAME
weak limits through the actual bounded comparison map. -/
theorem weakLimit_comparison {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {first : ℕ → E} {second : ℕ → F} {firstLimit : E} {secondLimit : F}
    (one : WeakConverges first firstLimit) (two : WeakConverges second secondLimit)
    (mapping : E →L[ℝ] F) (same : mapping ∘ first =ᶠ[atTop] second) :
    mapping firstLimit = secondLimit :=
  ((one.map mapping).congr same).unique two

/-- Lower semicontinuity retains the already uniform bound; no norm of a
restriction or observation map is inserted into the constant. -/
theorem WeakConverges.norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {sequence : ℕ → H} {limit : H} (convergence : WeakConverges sequence limit)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ᶠ n in atTop, ‖sequence n‖ ≤ constant) : ‖limit‖ ≤ constant := by
  let test := InnerProductSpace.toDual ℝ H limit
  have estimate : ∀ᶠ n in atTop, test (sequence n) ≤ ‖limit‖ * constant := by
    filter_upwards [bounded] with n hn
    calc
      _ ≤ ‖test (sequence n)‖ := le_abs_self _
      _ ≤ ‖test‖ * ‖sequence n‖ := test.le_opNorm _
      _ ≤ ‖limit‖ * constant := by
        rw [show ‖test‖ = ‖limit‖ from (InnerProductSpace.toDual ℝ H).norm_map limit]
        exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  have result := le_of_tendsto (convergence test) estimate
  have square : ‖limit‖ ^ 2 ≤ ‖limit‖ * constant := by
    simpa only [test, InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq] using result
  nlinarith [norm_nonneg limit]

theorem weakLimit_observation_bound {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {sequence : ℕ → E} {limit : E} (convergence : WeakConverges sequence limit)
    (observation : E →L[ℝ] H) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ᶠ n in atTop, ‖observation (sequence n)‖ ≤ constant) :
    ‖observation limit‖ ≤ constant :=
  (convergence.map observation).norm_le constant nonnegative bounded

end Grad.AnnularWeakExhaustion
