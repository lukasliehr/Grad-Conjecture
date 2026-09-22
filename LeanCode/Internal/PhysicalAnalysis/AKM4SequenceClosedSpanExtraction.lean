import AKM3WeakComparisonAndUniformBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion

/-- Separability is needed only in the closed span of the actual countable
sequence. Thus extraction in the full graph does not require rebuilding
its ambient L2 separability infrastructure. -/
theorem countableHilbert_weakExtraction
    (H : ℕ → Type*) [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)] [∀ k, CompleteSpace (H k)]
    (sequence : ∀ k, ℕ → H k) (constant : ℕ → ℝ)
    (bounded : ∀ k n, ‖sequence k n‖ ≤ constant k) :
    ∃ (limit : ∀ k, H k) (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∀ k, ‖limit k‖ ≤ constant k ∧ WeakConverges (sequence k ∘ subsequence) (limit k) := by
  let graph := fun k => (Submodule.span ℝ (range (sequence k))).topologicalClosure
  have closed (k : ℕ) : IsClosed (graph k : Set (H k)) :=
    (Submodule.span ℝ (range (sequence k))).isClosed_topologicalClosure
  let : ∀ k, CompleteSpace (graph k) := fun k => (closed k).completeSpace_coe
  have separable (k : ℕ) : TopologicalSpace.IsSeparable (graph k : Set (H k)) :=
    (countable_range (sequence k)).isSeparable.span.closure
  let : ∀ k, TopologicalSpace.SeparableSpace (graph k) := fun k => (separable k).separableSpace
  let contained : ∀ k, ℕ → graph k := fun k n =>
    ⟨sequence k n, (Submodule.span ℝ (range (sequence k))).le_topologicalClosure
      (Submodule.subset_span (mem_range_self n))⟩
  obtain ⟨limit, subsequence, increasing, limits⟩ :=
    countableHilbert_bounded_subsequence (fun k => graph k) contained constant bounded
  refine ⟨fun k => (limit k).val, subsequence, increasing, ?_⟩
  intro k
  refine ⟨(limits k).1, ?_⟩
  exact ((limits k).2.map (graph k).subtypeL)

end Grad.AnnularWeakExhaustion
