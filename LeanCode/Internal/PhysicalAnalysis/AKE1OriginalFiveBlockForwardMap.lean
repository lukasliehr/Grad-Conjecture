import AKA6FullOriginalBoundaryCoordinates
import AJE51OriginalMeanFreeRetraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularForwardDatum
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.ActualBoundaryPrimitives Grad.AnnularVariational Grad.AnnularReconstruction
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed

/-- The four original copied graph coordinates F0, F2, full F1 and strengthened G3. -/
abbrev ForwardSourceBlocks (parameters : PhaseParameters) (lower : ℝ) :=
  WithLp 2 (HighKnownGraphHilbert parameters lower ×
    WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))

/-- Literal original five-block graph carrier, independent of any smooth-core definition. -/
abbrev ForwardFiveBlocks (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :=
  WithLp 2 (OriginalCoupledSpace lower length positive × ForwardSourceBlocks parameters lower)

local instance forwardSourcesRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (ForwardSourceBlocks parameters lower) := by
  letI : NormedSpace ℝ (HighKnownGraphHilbert parameters lower) := inferInstance
  letI : NormedSpace ℝ (WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)) := inferInstance
  exact inferInstance
local instance forwardSourcesRealModule (parameters : PhaseParameters) (lower : ℝ) :
    Module ℝ (ForwardSourceBlocks parameters lower) :=
  (forwardSourcesRealNormed parameters lower).toModule
local instance forwardFiveRealNormed (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (ForwardFiveBlocks parameters lower length positive) := inferInstance
local instance forwardFiveRealModule (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    Module ℝ (ForwardFiveBlocks parameters lower length positive) :=
  (forwardFiveRealNormed parameters lower length positive).toModule
local instance forwardBoundaryRealNormed (parameters : PhaseParameters) :
    NormedSpace ℝ (OriginalBoundaryCoordinates parameters) :=
  NormedSpace.restrictScalars ℝ ℂ (OriginalBoundaryCoordinates parameters)
local instance forwardBoundaryRealModule (parameters : PhaseParameters) :
    Module ℝ (OriginalBoundaryCoordinates parameters) :=
  (forwardBoundaryRealNormed parameters).toModule

section Generic
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def forwardHilbertFirst : WithLp 2 (E × F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

def forwardHilbertSecond : WithLp 2 (E × F) →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

def forwardHilbertPair (first : D →L[ℝ] E) (second : D →L[ℝ] F) : D →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp (first.prod second)

theorem forwardHilbertPair_apply (first : D →L[ℝ] E) (second : D →L[ℝ] F) (input : D) :
    forwardHilbertPair first second input = WithLp.toLp 2 (first input,second input) := rfl
end Generic

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

/-- The accepted three original boundary traces packaged as a real continuous linear map. -/
def originalBoundaryTraceLinear : OriginalTraceInput parameters length lower positive →L[ℝ]
    OriginalBoundaryCoordinates parameters :=
  forwardHilbertPair
    (originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state)
    (forwardHilbertPair
      (((originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ _ _))
      (((originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ _ _)))

theorem originalBoundaryTraceLinear_apply (input : OriginalTraceInput parameters length lower positive) :
    originalBoundaryTraceLinear parameters length compact lower positive lowerHalf lengthPositive state input =
      originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input := rfl

/-- Extract exactly the retained candidate and its copied F0/F2 graphs. -/
def forwardTraceInput : ForwardFiveBlocks parameters lower length positive →L[ℝ]
    OriginalTraceInput parameters length lower positive :=
  forwardHilbertFirst.prod (forwardHilbertFirst.comp forwardHilbertSecond)

theorem forwardTraceInput_apply (input : ForwardFiveBlocks parameters lower length positive) :
    forwardTraceInput parameters length lower positive input = (input.ofLp.1,input.ofLp.2.ofLp.1) := rfl

/-- Append the full physical boundary triple to the unchanged four original graph blocks. -/
def originalForwardAmbient : ForwardFiveBlocks parameters lower length positive →L[ℝ]
    OriginalStrongAmbient parameters lower 0 0 :=
  forwardHilbertPair forwardHilbertSecond
    ((originalBoundaryTraceLinear parameters length compact lower positive lowerHalf lengthPositive state).comp
      (forwardTraceInput parameters length lower positive))

theorem originalForwardAmbient_apply (input : ForwardFiveBlocks parameters lower length positive) :
    originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state input =
      WithLp.toLp 2 (input.ofLp.2,
        originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
          (input.ofLp.1,input.ofLp.2.ofLp.1)) := rfl

/-- Bounded forward reconstruction of the full original datum. The accepted
retraction imposes only the original F2/f/g mean constraints, leaving F0 unrestricted. -/
def originalForwardDatum : ForwardFiveBlocks parameters lower length positive →L[ℝ]
    OriginalStrongCarrier parameters lower 0 0 :=
  (originalMeanFreeRetraction parameters lower).comp
    (originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state)

theorem originalForwardDatum_apply (input : ForwardFiveBlocks parameters lower length positive) :
    originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input =
      originalMeanFreeRetraction parameters lower
        (WithLp.toLp 2 (input.ofLp.2,
          originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
            (input.ofLp.1,input.ofLp.2.ofLp.1))) := rfl

end Grad.AnnularForwardDatum
