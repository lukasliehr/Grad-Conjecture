import AKM1RealHilbertWeakExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion

/-- One subsequence works in every member of a countable family of actual
Hilbert spaces. Compact metrizable weak-dual balls implement the exact
diagonal without identifying different annulus or grade carriers. -/
theorem countableHilbert_bounded_subsequence
    (H : ℕ → Type*) [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)] [∀ k, CompleteSpace (H k)]
    [∀ k, TopologicalSpace.SeparableSpace (H k)]
    (sequence : ∀ k, ℕ → H k) (constant : ℕ → ℝ)
    (bounded : ∀ k n, ‖sequence k n‖ ≤ constant k) :
    ∃ (limit : ∀ k, H k) (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∀ k, ‖limit k‖ ≤ constant k ∧ WeakConverges (sequence k ∘ subsequence) (limit k) := by
  let ball := fun k => WeakDual.toStrongDual ⁻¹'
    Metric.closedBall (0 : StrongDual ℝ (H k)) (constant k)
  have compact (k : ℕ) : IsCompact (ball k) :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ (H k)) (constant k)
  let : ∀ k, CompactSpace (ball k) := fun k => isCompact_iff_compactSpace.mp (compact k)
  let : ∀ k, TopologicalSpace.MetrizableSpace (ball k) := fun k =>
    WeakDual.metrizable_of_isCompact ℝ (H k) (ball k) (compact k)
  let dualSequence : ℕ → ∀ k, ball k := fun n k =>
    ⟨(InnerProductSpace.toDual ℝ (H k) (sequence k n)).toWeakDual, by
      simpa only [ball, mem_preimage, Metric.mem_closedBall, dist_zero_right,
        StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using bounded k n⟩
  obtain ⟨dual, subsequence, increasing, convergence⟩ := CompactSpace.tendsto_subseq dualSequence
  let limit := fun k => (InnerProductSpace.toDual ℝ (H k)).symm (dual k).val.toStrongDual
  refine ⟨limit, subsequence, increasing, ?_⟩
  intro k
  constructor
  · simpa only [limit, LinearIsometryEquiv.norm_map, ball, mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using (dual k).property
  · intro test
    have evaluation : Continuous (fun point : ∀ k, ball k =>
        (point k).val ((InnerProductSpace.toDual ℝ (H k)).symm test)) :=
      (WeakDual.eval_continuous _).comp (continuous_subtype_val.comp (continuous_apply k))
    have evaluated := evaluation.tendsto dual |>.comp convergence
    simpa only [Function.comp_def, rieszWeakEvaluation, dualSequence,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.symm_apply_apply, limit] using evaluated

end Grad.AnnularWeakExhaustion
