import AKE2ForwardDatumBoundsAndCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularForwardDatum
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.ActualBoundaryPrimitives Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

/-- Observe precisely the retained candidate and four original copied graphs. -/
def originalFiveBlockObservation (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive) :
    ForwardFiveBlocks parameters lower length positive := WithLp.toLp 2 (candidate,data.val.ofLp.1)

private theorem hilbertPair_of_coordinates {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (field : WithLp 2 (E × F)) (second : F) (same : second = field.ofLp.2) :
    WithLp.toLp 2 (field.ofLp.1,second) = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E F).injective
  exact Prod.ext rfl same

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

include small in
/-- On every solution of the original full sourced equation, the constructed
ambient datum recovers all four copied graphs and every original boundary coordinate. -/
theorem originalForwardAmbient_of_equation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state
      (originalFiveBlockObservation parameters lower length positive data candidate) = data.val := by
  apply hilbertPair_of_coordinates
  exact originalBoundaryTrace_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small data candidate equation

include small in
/-- Exact original datum recovery, with no smooth-core or density premise. -/
theorem originalForwardDatum_of_equation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state
      (originalFiveBlockObservation parameters lower length positive data candidate) = data := by
  exact (congrArg (originalMeanFreeRetraction parameters lower)
    (originalForwardAmbient_of_equation parameters length compact lower positive lowerHalf lengthPositive state
      widthHalf widthLength small data candidate equation)).trans
        (originalMeanFreeRetraction_fixed parameters lower positive (lowerHalf.trans (by norm_num)) data)

/-- Left inverse on the SAME original shared response, with unchanged original widths and B8 ball. -/
theorem originalForwardDatum_response (data : OriginalStrongCarrier parameters lower 0 0) :
    originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state
      (originalFiveBlockObservation parameters lower length positive data
        (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) = data :=
  originalForwardDatum_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small data _
      (originalSharedResponse_equation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)

end Grad.AnnularForwardDatum
