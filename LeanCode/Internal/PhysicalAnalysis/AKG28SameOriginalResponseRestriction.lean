import AKG27ActualOriginalEquationRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularReconstruction Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

/-- Exact five-block observation commutes with restriction. This retains the
actual derivative/flux graph coordinates and every copied original source. -/
theorem originalEndpointDatum_observation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    originalFiveBlockObservation parameters upper length upperPositive
      (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
        (originalFiveBlockObservation parameters lower length lowerPositive data candidate))
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate) =
    originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included
      (originalFiveBlockObservation parameters lower length lowerPositive data candidate) := by
  exact congrArg (fun sources : ForwardSourceBlocks parameters upper => WithLp.toLp 2
    (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate,sources))
    (originalEndpointDatum_sources parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate)

include small in
/-- The SAME original response restricted to the smaller collar is exactly
the existing shared inverse applied to its reconstructed original datum. -/
theorem originalEndpointDatum_sameResponse (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state data candidate) :
    originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate =
      originalSharedResponse parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state small
        (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
          (originalFiveBlockObservation parameters lower length lowerPositive data candidate)) :=
  originalSharedResponse_unique parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state small _ _
    (originalEndpointDatum_equation parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
      widthHalf widthLength small data candidate equation)

include small in
/-- Full original outer datum h is unchanged. This includes the actual known
source boundary term and low physical boundary contribution. -/
theorem originalEndpointDatum_outer_preserved (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state data candidate) :
    (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
      (originalFiveBlockObservation parameters lower length lowerPositive data candidate)).val.ofLp.2.ofLp.1 = data.val.ofLp.2.ofLp.1 := by
  have original := congrArg (fun value : OriginalBoundaryCoordinates parameters => value.ofLp.1)
    (originalBoundaryTrace_of_equation parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state
      widthHalf widthLength small data candidate equation)
  have rebuilt := congrArg (fun value : OriginalBoundaryCoordinates parameters => value.ofLp.1)
    (originalForwardDatum_boundary parameters length compact upper upperPositive upperHalf lengthPositive state
      (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included
        (originalFiveBlockObservation parameters lower length lowerPositive data candidate)))
  exact rebuilt.trans ((originalRetainedRestriction_fullOuter lower upper length lowerPositive upperPositive upperHalf included parameters lengthPositive compact state
    candidate data.val.ofLp.1.ofLp.1).trans original)

end Grad.AnnularRestriction
