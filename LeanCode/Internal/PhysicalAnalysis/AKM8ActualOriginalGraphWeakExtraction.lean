import AKM7OriginalEquationGraphProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularForwardDatum Grad.AnnularForwardTraces
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

/-- The exact full original equation graphs admit one simultaneous weak
exhaustion subsequence. Fixed-collar bounds supply compactness only; this
statement does not manufacture a radius-uniform retained estimate. -/
theorem originalEquationGraphs_countable_weakExtraction
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (lower : ℕ → ℝ) (positive : ∀ k, 0 < lower k) (lowerHalf : ∀ k, lower k ≤ 1 / 2)
    (sequence : ∀ k, ℕ → OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (constant : ℕ → ℝ) (bounded : ∀ k n, ‖sequence k n‖ ≤ constant k)
    (equations : ∀ k, ∀ᶠ n in atTop, sequence k n ∈
      OriginalObservedEquationGraph parameters length compact (lower k) (positive k) (lowerHalf k)
        lengthPositive widthHalf widthLength state) :
    ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
      (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∀ k, ‖limit k‖ ≤ constant k ∧ WeakConverges (sequence k ∘ subsequence) (limit k) ∧
        limit k ∈ OriginalObservedEquationGraph parameters length compact (lower k) (positive k)
          (lowerHalf k) lengthPositive widthHalf widthLength state := by
  obtain ⟨limit, subsequence, increasing, limits⟩ :=
    originalFiveBlocks_countable_weakExtraction parameters length lower positive sequence constant bounded
  refine ⟨limit, subsequence, increasing, ?_⟩
  intro k
  refine ⟨(limits k).1, (limits k).2, ?_⟩
  apply originalObservedEquationGraph_weak_limit parameters length compact (lower k) (positive k)
    (lowerHalf k) lengthPositive widthHalf widthLength state small (limits k).2
  exact increasing.tendsto_atTop.eventually (equations k)

end Grad.AnnularWeakExhaustion
