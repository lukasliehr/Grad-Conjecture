import AKBM26ExactOriginalHomogeneousGraphConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length) (state : RetainedInverseState parameters length compact)

/-- The literal combined high and low outer seven tuple of the SAME
completed graph candidate and copied source graphs. -/
def originalFullOuterSeven (candidate : CoupledSpace lower length positive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower) : SevenSlotTrace parameters 0 0 :=
  sevenSlotTrace parameters 0 0
    (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val
    (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1)
    (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp)+
  lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2

/-- The complete original outer row is one actual BCT physical boundary
operator on the full seven tuple; its low contribution is included. -/
theorem originalFullOuterSeven_boundary (candidate : CoupledSpace lower length positive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state candidate graphs=
      lowStateBoundaryPR parameters length compact state
        (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs) := by
  change lowStateBoundaryPR parameters length compact state _+lowStateBoundaryPR parameters length compact state _=
    lowStateBoundaryPR parameters length compact state (_+_)
  exact (map_add _ _ _).symm

/-- The same exact full-seven identity in the original graph coordinates. -/
theorem originalOuterBoundary_fullSeven (candidate : OriginalCoupledSpace lower length positive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state (candidate,graphs)=
      lowStateBoundaryPR parameters length compact state
        (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive
          (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) graphs) := by
  rw [originalOuterBoundaryTrace_to_coupled,originalFullOuterSeven_boundary]

end Grad.OriginalKernelOuterUniqueness
