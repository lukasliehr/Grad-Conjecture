import AKA1BoundedOriginalBoundaryTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.AnnularForwardTraces
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentBoundary Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse Grad.BoundaryKernelAction
open Grad.AnnularReconstruction Grad.AnnularPhysicalSolution Grad.AnnularStrongOrbit Grad.AnnularCurrentSource

local instance traceOriginalRealNormed (lower length : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (OriginalCoupledSpace lower length positive) :=
  NormedSpace.restrictScalars ℝ ℂ (OriginalCoupledSpace lower length positive)
local instance traceOriginalRealModule (lower length : ℝ) (positive : 0 < lower) :
    Module ℝ (OriginalCoupledSpace lower length positive) :=
  (traceOriginalRealNormed lower length positive).toModule
local instance traceCoupledRealNormed (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    NormedSpace ℝ (CoupledSpace lower length positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CoupledSpace lower length positive lengthPositive)
local instance traceCoupledRealModule (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    Module ℝ (CoupledSpace lower length positive lengthPositive) :=
  (traceCoupledRealNormed lower length positive lengthPositive).toModule

theorem graphNativePhysicalBoundary_blocks {parameters : PhaseParameters} {length compact : ℝ}
    (state : BoundaryInverseState parameters length compact)
    (x : HighBoundaryPrimitive parameters 0 0) (xi : PositiveTrace parameters 0 0 1)
    (source : SourceBoundaryTuple) :
    graphNativePhysicalBoundary state 0 0 x xi source =
      actualBoundaryTOnHigh state.val 0 0 x +
        actualBoundaryNOnHigh state.val 0 0 (originalRetainedBoundaryVector parameters length 0 0 xi) +
        actualBoundaryHOnHigh state.val 0 0 (graphSourceBoundaryVector parameters 0 0 source) := by
  have decomposition := actualPhysicalBoundary_block_equation state.val 0 0
    (sevenSlotTrace parameters 0 0 x.val xi source) x.property
  rw [boundaryRetainedVector_sevenSlot parameters length,boundarySourceVector_sevenSlot] at decomposition
  exact Subtype.ext decomposition

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

/-- The fixed-collar input for all forward traces: an arbitrary retained
candidate and the two actual copied source graphs. -/
abbrev OriginalTraceInput :=
  OriginalCoupledSpace lower length positive × HighKnownGraphHilbert parameters lower

private def weightedTraceCandidate : OriginalTraceInput parameters length lower positive →L[ℝ]
    CoupledSpace lower length positive lengthPositive :=
  ((originalCoupledEquivalence parameters lower length positive
    (lowerHalf.trans (by norm_num)) lengthPositive).toContinuousLinearMap.restrictScalars ℝ).comp
      (ContinuousLinearMap.fst ℝ _ _)

/-- Full original outer h in its original P_R norm. The source graph term
and the actual low physical boundary contribution are both retained. -/
def originalOuterBoundaryTrace : OriginalTraceInput parameters length lower positive →L[ℝ]
    HighBoundaryPrimitive parameters 0 0 :=
  ((actualBoundaryTOnHigh state.outerInverseState.val 0 0).restrictScalars ℝ).comp
    (((coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive).restrictScalars ℝ).comp
      (weightedTraceCandidate parameters length lower positive lowerHalf lengthPositive)) +
  ((actualBoundaryNOnHigh state.outerInverseState.val 0 0).restrictScalars ℝ).comp
    (((originalRetainedBoundaryLinear parameters length lengthPositive 0 0).restrictScalars ℝ).comp
      (((coupledHighXiOuter parameters lower length positive lowerHalf lengthPositive).restrictScalars ℝ).comp
        (weightedTraceCandidate parameters length lower positive lowerHalf lengthPositive))) +
  ((actualBoundaryHOnHigh state.outerInverseState.val 0 0).restrictScalars ℝ).comp
    (((graphSourceBoundaryVectorMap parameters 0 0).restrictScalars ℝ).comp
      ((highGraphOuterTupleMap parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0).comp
        (ContinuousLinearMap.snd ℝ _ _))) +
  ((lowStateBoundaryPR parameters length compact state).restrictScalars ℝ).comp
    (((lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf).restrictScalars ℝ).comp
      ((traceHilbertSecond.restrictScalars ℝ).comp
        (weightedTraceCandidate parameters length lower positive lowerHalf lengthPositive)))

/-- The literal full physical outer boundary of a coupled candidate and
its copied source graphs, before the original coordinate equivalence. -/
def coupledFullOuterBoundary (candidate : CoupledSpace lower length positive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower) : HighBoundaryPrimitive parameters 0 0 :=
  graphNativePhysicalBoundary state.outerInverseState 0 0
    (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate)
    (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1)
    (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp) +
  lowStateBoundaryPR parameters length compact state
    (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2)

theorem originalOuterBoundaryTrace_apply
    (candidate : OriginalCoupledSpace lower length positive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state (candidate,graphs) =
      let weighted := originalCoupledEquivalence parameters lower length positive
        (lowerHalf.trans (by norm_num)) lengthPositive candidate
      graphNativePhysicalBoundary state.outerInverseState 0 0
        (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive weighted)
        (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 weighted.ofLp.1.ofLp.1)
        (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp) +
      lowStateBoundaryPR parameters length compact state
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf weighted.ofLp.2) := by
  let weighted := originalCoupledEquivalence parameters lower length positive
    (lowerHalf.trans (by norm_num)) lengthPositive candidate
  let x := coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive weighted
  let xi := actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 weighted.ofLp.1.ofLp.1
  let source := highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp
  let low := lowStateBoundaryPR parameters length compact state
    (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf weighted.ofLp.2)
  have sourceLaw : graphSourceBoundaryVectorMap parameters 0 0
      (highGraphOuterTupleMap parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs) =
      graphSourceBoundaryVector parameters 0 0 source :=
    (graphSourceBoundaryVectorMap_apply parameters 0 0 _).trans
      (congrArg (graphSourceBoundaryVector parameters 0 0)
        (highGraphOuterTupleMap_apply parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs))
  change actualBoundaryTOnHigh state.outerInverseState.val 0 0 x +
    actualBoundaryNOnHigh state.outerInverseState.val 0 0
      (originalRetainedBoundaryLinear parameters length lengthPositive 0 0 xi) +
    actualBoundaryHOnHigh state.outerInverseState.val 0 0
      (graphSourceBoundaryVectorMap parameters 0 0
        (highGraphOuterTupleMap parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs)) + low =
    graphNativePhysicalBoundary state.outerInverseState 0 0 x xi source + low
  rw [originalRetainedBoundaryLinear_apply,sourceLaw,← graphNativePhysicalBoundary_blocks]


theorem originalOuterBoundaryTrace_to_coupled
    (candidate : OriginalCoupledSpace lower length positive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state (candidate,graphs) =
      coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state
        (originalCoupledEquivalence parameters lower length positive
          (lowerHalf.trans (by norm_num)) lengthPositive candidate) graphs :=
  originalOuterBoundaryTrace_apply parameters length compact lower positive lowerHalf lengthPositive state candidate graphs

/-- A genuine fixed-collar bound, derived from the constructed continuous
linear operator on the exact original normed carriers. -/
theorem originalOuterBoundaryTrace_bound (input : OriginalTraceInput parameters length lower positive) :
    ‖originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
      ‖originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state‖ * ‖input‖ :=
  (originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state).le_opNorm input

end Grad.AnnularForwardTraces
