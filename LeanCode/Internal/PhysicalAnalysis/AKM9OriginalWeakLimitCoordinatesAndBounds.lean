import AKM8ActualOriginalGraphWeakExtraction
import AKL1LiteralExhaustionWeightedNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularExhaustionEstimate
open Grad.ActualBoundaryPrimitives
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner
  weakOriginalDataRealNormed weakOriginalDataRealModule

local instance weakWeightedRetainedRealInner (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) : InnerProductSpace ℝ (CoupledSpace lower length positive lengthPositive) :=
  InnerProductSpace.rclikeToReal ℂ (CoupledSpace lower length positive lengthPositive)
local instance weakOuterRealInner (parameters : PhaseParameters) :
    InnerProductSpace ℝ (HighBoundaryPrimitive parameters 0 0) :=
  InnerProductSpace.rclikeToReal ℂ (HighBoundaryPrimitive parameters 0 0)

theorem weakLimit_eventuallyConstant {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {sequence : ℕ → E} {limit : E} (convergence : WeakConverges sequence limit)
    (mapping : E →L[ℝ] H) (value : H)
    (same : ∀ᶠ n in atTop, mapping (sequence n) = value) : mapping limit = value :=
  weakLimit_comparison convergence (fun _ => tendsto_const_nhds) mapping same

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)

/-- The exact native weighted retained observation of all five original blocks. -/
def originalWeightedRetainedObservation : OriginalFiveBlockAmbient parameters lower length positive →L[ℝ]
    CoupledSpace lower length positive lengthPositive :=
  ((originalCoupledEquivalence parameters lower length positive bounded lengthPositive).toContinuousLinearMap.restrictScalars ℝ).comp
    forwardHilbertFirst

theorem originalWeightedRetainedObservation_apply
    (field : OriginalFiveBlockAmbient parameters lower length positive) :
    originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive field =
      originalWeightedRetained parameters lower length positive bounded lengthPositive field.ofLp.1 := rfl

/-- The actual EX retained bound passes to the full-graph weak limit with
the identical constant, even when the observation has a collar-dependent norm. -/
theorem originalWeightedRetainedNorm_weak_limit
    {sequence : ℕ → OriginalFiveBlockAmbient parameters lower length positive}
    {limit : OriginalFiveBlockAmbient parameters lower length positive}
    (convergence : WeakConverges sequence limit) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (estimate : ∀ᶠ n in atTop, originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive
      (sequence n).ofLp.1 ≤ constant) :
    originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive limit.ofLp.1 ≤ constant :=
  weakLimit_observation_bound convergence
    (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive)
    constant nonnegative estimate

omit bounded lengthPositive in
/-- The entire copied-source/full-residual tuple survives an eventually
constant source sequence. No source coordinate is discarded before extraction. -/
theorem originalFullSources_weak_limit
    {sequence : ℕ → OriginalFiveBlockAmbient parameters lower length positive}
    {limit : OriginalFiveBlockAmbient parameters lower length positive}
    (convergence : WeakConverges sequence limit) (sources : OriginalFullSourceBlocks parameters lower)
    (same : ∀ᶠ n in atTop, (sequence n).ofLp.2 = sources) : limit.ofLp.2 = sources :=
  weakLimit_eventuallyConstant convergence forwardHilbertSecond sources same

omit bounded in
/-- The original physical outer row is weakly preserved, including its
copied-source term and low-mode contribution. Only the outer row is fixed. -/
theorem originalFullOuter_weak_limit (compact : ℝ) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact)
    {sequence : ℕ → OriginalFiveBlockAmbient parameters lower length positive}
    {limit : OriginalFiveBlockAmbient parameters lower length positive}
    (convergence : WeakConverges sequence limit) (outer : HighBoundaryPrimitive parameters 0 0)
    (same : ∀ᶠ n in atTop,
      originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
        ((sequence n).ofLp.1, (sequence n).ofLp.2.ofLp.1) = outer) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (limit.ofLp.1, limit.ofLp.2.ofLp.1) = outer :=
  weakLimit_eventuallyConstant convergence
    ((originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state).comp
      (forwardTraceInput parameters length lower positive)) outer same

end Grad.AnnularWeakExhaustion
