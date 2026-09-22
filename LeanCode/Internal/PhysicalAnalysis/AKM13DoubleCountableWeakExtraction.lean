import AKM10OriginalRestrictionWeakLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion

/-- Reindex the checked countable extraction over actual collar/grade pairs.
Every pair keeps its own Hilbert carrier and bound. -/
theorem doubleCountableHilbert_weakExtraction
    (H : ℕ → ℕ → Type*) [∀ k t, NormedAddCommGroup (H k t)]
    [∀ k t, InnerProductSpace ℝ (H k t)] [∀ k t, CompleteSpace (H k t)]
    (sequence : ∀ k t, ℕ → H k t) (constant : ℕ → ℕ → ℝ)
    (bounded : ∀ k t n, ‖sequence k t n‖ ≤ constant k t) :
    ∃ (limit : ∀ k t, H k t) (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∀ k t, ‖limit k t‖ ≤ constant k t ∧ WeakConverges (sequence k t ∘ subsequence) (limit k t) := by
  obtain ⟨encodedLimit, subsequence, increasing, limits⟩ :=
    countableHilbert_weakExtraction (fun n => H (Nat.unpair n).1 (Nat.unpair n).2)
      (fun n => sequence (Nat.unpair n).1 (Nat.unpair n).2)
      (fun n => constant (Nat.unpair n).1 (Nat.unpair n).2)
      (fun n stage => bounded (Nat.unpair n).1 (Nat.unpair n).2 stage)
  have decoded (k t : ℕ) : ∃ limit : H k t,
      ‖limit‖ ≤ constant k t ∧ WeakConverges (sequence k t ∘ subsequence) limit := by
    have encoded : ∃ limit : H (Nat.unpair (Nat.pair k t)).1 (Nat.unpair (Nat.pair k t)).2,
        ‖limit‖ ≤ constant (Nat.unpair (Nat.pair k t)).1 (Nat.unpair (Nat.pair k t)).2 ∧
        WeakConverges (sequence (Nat.unpair (Nat.pair k t)).1 (Nat.unpair (Nat.pair k t)).2 ∘ subsequence) limit :=
      ⟨encodedLimit (Nat.pair k t), limits (Nat.pair k t)⟩
    have transport := congrArg (fun pair : ℕ × ℕ => ∃ limit : H pair.1 pair.2,
      ‖limit‖ ≤ constant pair.1 pair.2 ∧ WeakConverges (sequence pair.1 pair.2 ∘ subsequence) limit)
      (Nat.unpair_pair k t)
    exact transport.mp encoded
  exact ⟨fun k t => (decoded k t).choose, subsequence, increasing, fun k t => (decoded k t).choose_spec⟩

theorem WeakConverges.subsequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {sequence : ℕ → E} {limit : E} (convergence : WeakConverges sequence limit)
    (subsequence : ℕ → ℕ) (increasing : StrictMono subsequence) :
    WeakConverges (sequence ∘ subsequence) limit :=
  fun test => (convergence test).comp increasing.tendsto_atTop

end Grad.AnnularWeakExhaustion
