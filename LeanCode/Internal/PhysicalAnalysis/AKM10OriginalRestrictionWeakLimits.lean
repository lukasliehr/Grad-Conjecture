import AKM9OriginalWeakLimitCoordinatesAndBounds
import AKG28SameOriginalResponseRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularStrongSolution
open Grad.AnnularRestriction Grad.AnnularExhaustionEstimate
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)

/-- The full original restriction of the weak limit is the weak limit of
all five restricted blocks, including the two entire copied source graphs. -/
theorem originalFiveBlockRestriction_weak_limit
    {sequence : ℕ → OriginalFiveBlockAmbient parameters lower length lowerPositive}
    {limit : OriginalFiveBlockAmbient parameters lower length lowerPositive}
    (convergence : WeakConverges sequence limit) :
    WeakConverges
      ((originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included) ∘ sequence)
      (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included limit) :=
  convergence.map (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included)

/-- Eventual SAME-field restriction identities survive simultaneous weak
extraction. New incoming data are the actual endpoint traces of this limit. -/
theorem originalFiveBlockLimits_compatible
    {first : ℕ → OriginalFiveBlockAmbient parameters lower length lowerPositive}
    {second : ℕ → OriginalFiveBlockAmbient parameters upper length upperPositive}
    {firstLimit : OriginalFiveBlockAmbient parameters lower length lowerPositive}
    {secondLimit : OriginalFiveBlockAmbient parameters upper length upperPositive}
    (one : WeakConverges first firstLimit) (two : WeakConverges second secondLimit)
    (same : ∀ᶠ n in atTop,
      originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included (first n) = second n) :
    originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included firstLimit = secondLimit :=
  weakLimit_comparison one two
    (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included) same

/-- Actual native retained contraction. The collar-dependent original
coordinate equivalence does not enter the uniform exhaustion constant. -/
theorem originalRestriction_weightedRetainedNorm
    (field : OriginalFiveBlockAmbient parameters lower length lowerPositive) :
    originalWeightedRetainedNorm parameters upper length upperPositive upperBounded.le lengthPositive
      (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).ofLp.1 ≤
    originalWeightedRetainedNorm parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field.ofLp.1 := by
  change ‖Grad.AnnularStrongSolution.originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
    (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field.ofLp.1)‖ ≤ _
  rw [originalRetainedRestriction_weighted]
  exact coupledEndpointRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included _

end Grad.AnnularWeakExhaustion
