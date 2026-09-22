import AKA2FullOriginalOuterBoundary
import AKA3GenuineFluxEndpointIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularForwardTraces
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentBoundary Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCurrentGreen Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularPhysicalSolution Grad.AnnularFullSource Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- The bounded completed trace is the SAME actual physical flux endpoint
of the sourced coupled response; no endpoint value is assigned independently. -/
theorem coupledHighFluxOuter_sameResponse
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower) :
    coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive
      (coupledKnownResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) =
      coupledPhysicalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData :=
  coupledHighFluxOuter_eq parameters lower length positive lengthPositive widthHalf widthLength lowerHalf
    (coupledKnownResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledPhysicalOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledPhysicalOutput_compact parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledPhysicalOutput_sameFlux parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledPhysicalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledPhysicalOutput_outerMoment parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)

/-- Full prescribed original h, including the known-source boundary and
the actual low-sector contribution, recovered from the SAME graph traces. -/
theorem sharedStrongResponse_originalOuter
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let highData := strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive response)
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 response.ofLp.1.ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 highData.graphs) +
      lowStateBoundaryPR parameters length compact state
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf response.ofLp.2) = highData.datum := by
  have same : coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) =
      coupledPhysicalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
        (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data) :=
    coupledHighFluxOuter_sameResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small _ _
  dsimp only
  rw [same]
  exact sharedStrongResponse_fullBoundary parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

theorem sharedStrongResponse_coupledFullOuter
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
      data.val.ofLp.1.ofLp.2.ofLp.1 =
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data).datum :=
  sharedStrongResponse_originalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

end Grad.AnnularForwardTraces
