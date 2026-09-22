import AKG26OriginalFullPhysicalEquationConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
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

/-- The rebuilt boundary is precisely the full original trace of the SAME
restricted retained candidate with its SAME copied source graphs. -/
theorem originalEndpointDatum_actualBoundary (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    let nextData := originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
      (originalFiveBlockObservation parameters lower length lowerPositive data candidate)
    let nextCandidate := originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
      (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate
    originalBoundaryTrace parameters length compact upper upperPositive upperHalf lengthPositive state
      (nextCandidate,nextData.val.ofLp.1.ofLp.1) = nextData.val.ofLp.2 := by
  dsimp only
  have sources := congrArg (fun value : ForwardSourceBlocks parameters upper => value.ofLp.1)
    (originalEndpointDatum_sources parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate)
  exact (congrArg (fun graphs => originalBoundaryTrace parameters length compact upper upperPositive upperHalf lengthPositive state
    (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
      (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate,graphs)) sources).trans
    (originalForwardDatum_boundary parameters length compact upper upperPositive upperHalf lengthPositive state
      (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included
        (originalFiveBlockObservation parameters lower length lowerPositive data candidate))).symm

/-- Genuine original equation locality. All five blocks are restricted, the
new independent incoming values are actual endpoint traces, and the full
variable-coefficient variational equation follows from the genuine weak rows. -/
theorem originalEndpointDatum_equation
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length lowerPositive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state data candidate) :
    OriginalStrongCoupledEquation parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state
      (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
        (originalFiveBlockObservation parameters lower length lowerPositive data candidate))
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate) := by
  let nextData := originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
    (originalFiveBlockObservation parameters lower length lowerPositive data candidate)
  have sources := originalEndpointDatum_sources parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate
  exact originalStrongEquation_of_fullPhysical parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state small nextData _
    (originalRestrictedCandidate_highOutput_eq_full parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included
      widthHalf widthLength state small data nextData sources candidate equation)
    (originalRestrictedCandidate_fullCompact parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included
      widthHalf widthLength state small data nextData sources candidate equation)
    (originalRestrictedCandidate_fullLowRow parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included
      widthHalf widthLength state small data nextData sources candidate equation)
    (originalEndpointDatum_actualBoundary parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate)

end Grad.AnnularRestriction
