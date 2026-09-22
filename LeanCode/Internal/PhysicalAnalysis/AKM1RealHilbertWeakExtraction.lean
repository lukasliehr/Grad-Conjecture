import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion

/-- Weak convergence tests every bounded real linear functional. -/
def WeakConverges {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sequence : ℕ → E) (limit : E) : Prop :=
  ∀ test : E →L[ℝ] ℝ, Tendsto (fun n => test (sequence n)) atTop (𝓝 (test limit))

theorem rieszWeakEvaluation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (dual : WeakDual ℝ H) (test : H →L[ℝ] ℝ) :
    dual ((InnerProductSpace.toDual ℝ H).symm test) =
      test ((InnerProductSpace.toDual ℝ H).symm dual.toStrongDual) := by
  let represented := (InnerProductSpace.toDual ℝ H).symm dual.toStrongDual
  have same := InnerProductSpace.toDual_symm_apply
    (x := (InnerProductSpace.toDual ℝ H).symm test) (y := dual.toStrongDual)
  rw [← WeakDual.toStrongDual_apply, ← same, real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply
    (x := represented) (y := test)

/-- A bounded sequence in an actual complete separable real Hilbert space
has a weakly convergent subsequence with the original bound. This uses the
pinned sequential Banach--Alaoglu and Riesz theorems, including finite and
zero-dimensional spaces. -/
theorem realHilbert_bounded_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (sequence : ℕ → H) (constant : ℝ)
    (bounded : ∀ n, ‖sequence n‖ ≤ constant) :
    ∃ (limit : H) (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ‖limit‖ ≤ constant ∧ WeakConverges (sequence ∘ subsequence) limit := by
  let dualSequence := fun n => (InnerProductSpace.toDual ℝ H (sequence n)).toWeakDual
  have membership (n : ℕ) : dualSequence n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) constant := by
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right,
      dualSequence, StrongDual.toStrongDual_toWeakDual,
      LinearIsometryEquiv.norm_map] using bounded n
  obtain ⟨dual, dualBound, subsequence, increasing, convergence⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) constant membership
  let limit := (InnerProductSpace.toDual ℝ H).symm dual.toStrongDual
  refine ⟨limit, subsequence, increasing, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm dual.toStrongDual‖ ≤ constant
    simpa only [LinearIsometryEquiv.norm_map, mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using dualBound
  · intro test
    have evaluated := (WeakDual.eval_continuous
      ((InnerProductSpace.toDual ℝ H).symm test)).tendsto dual |>.comp convergence
    simpa only [Function.comp_def, rieszWeakEvaluation, dualSequence,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.symm_apply_apply, limit] using evaluated

end Grad.AnnularWeakExhaustion
