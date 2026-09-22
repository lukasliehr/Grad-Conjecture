import AKM10OriginalRestrictionWeakLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

/-- One actual full-graph subsequence produces compatible original equation
solutions on every enumerated collar. All copied sources, full physical outer
data and the native retained estimate pass to these SAME limits. -/
theorem originalCompatibleEquationFamily_of_bounded_sequence
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (lower : ℕ → ℝ) (positive : ∀ k, 0 < lower k) (lowerHalf : ∀ k, lower k ≤ 1 / 2)
    (sequence : ∀ k, ℕ → OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (constant : ℕ → ℝ) (bounded : ∀ k n, ‖sequence k n‖ ≤ constant k)
    (sources : ∀ k, OriginalFullSourceBlocks parameters (lower k))
    (outer : HighBoundaryPrimitive parameters 0 0)
    (retainedBound : ℝ) (retainedNonnegative : 0 ≤ retainedBound)
    (equations : ∀ k, ∀ᶠ n in atTop, sequence k n ∈ OriginalObservedEquationGraph parameters length compact
      (lower k) (positive k) (lowerHalf k) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ k, ∀ᶠ n in atTop, (sequence k n).ofLp.2 = sources k)
    (sameOuter : ∀ k, ∀ᶠ n in atTop,
      originalOuterBoundaryTrace parameters length compact (lower k) (positive k) (lowerHalf k) lengthPositive state
        ((sequence k n).ofLp.1, (sequence k n).ofLp.2.ofLp.1) = outer)
    (retained : ∀ k, ∀ᶠ n in atTop,
      originalWeightedRetainedNorm parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive
        (sequence k n).ofLp.1 ≤ retainedBound)
    (compatible : ∀ k l (included : lower k ≤ lower l), ∀ᶠ n in atTop,
      originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
        ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (sequence k n) = sequence l n) :
    ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
      (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      (∀ k, WeakConverges (sequence k ∘ subsequence) (limit k)) ∧
      (∀ k, limit k ∈ OriginalObservedEquationGraph parameters length compact (lower k) (positive k)
        (lowerHalf k) lengthPositive widthHalf widthLength state ∧
        (limit k).ofLp.2 = sources k ∧
        originalOuterBoundaryTrace parameters length compact (lower k) (positive k) (lowerHalf k) lengthPositive state
          ((limit k).ofLp.1, (limit k).ofLp.2.ofLp.1) = outer ∧
        originalWeightedRetainedNorm parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive
          (limit k).ofLp.1 ≤ retainedBound) ∧
      (∀ k l (included : lower k ≤ lower l),
        originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
          ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (limit k) = limit l) := by
  obtain ⟨limit, subsequence, increasing, limits⟩ := originalEquationGraphs_countable_weakExtraction
    parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf sequence constant bounded equations
  refine ⟨limit, subsequence, increasing, fun k => (limits k).2.1, ?_, ?_⟩
  · intro k
    refine ⟨(limits k).2.2, ?_, ?_, ?_⟩
    · exact originalFullSources_weak_limit parameters (lower k) length (positive k) (limits k).2.1 (sources k)
        (increasing.tendsto_atTop.eventually (sameSources k))
    · exact originalFullOuter_weak_limit parameters (lower k) length (positive k) lengthPositive compact (lowerHalf k) state
        (limits k).2.1 outer (increasing.tendsto_atTop.eventually (sameOuter k))
    · exact originalWeightedRetainedNorm_weak_limit parameters (lower k) length (positive k)
        ((lowerHalf k).trans (by norm_num)) lengthPositive (limits k).2.1 retainedBound retainedNonnegative
        (increasing.tendsto_atTop.eventually (retained k))
  · intro k l included
    exact originalFiveBlockLimits_compatible parameters (lower k) (lower l) length (positive k) (positive l)
      ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (limits k).2.1 (limits l).2.1
      (increasing.tendsto_atTop.eventually (compatible k l included))

end Grad.AnnularWeakExhaustion
