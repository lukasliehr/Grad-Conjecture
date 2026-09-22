import AKI35ArbitraryHighCompactConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularOriginalSmoothCore
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularCoupledInverse Grad.AnnularFullGraph Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularRestriction Grad.AnnularForwardTraces
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

include represented small

/-- Literal four-field AH24 representation and the original boundary traces
imply the original variational equation for this arbitrary candidate. Every
interior equation is derived from the tuple, not included in the core predicate. -/
theorem OriginalTupleObservation.originalEquation
    (boundary : originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (candidate,data.val.ofLp.1.ofLp.1) = data.val.ofLp.2) :
    OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate := by
  apply originalStrongEquation_of_fullPhysical parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data candidate
  · rw [originalStrongWeightEquivalence_eq_reconstruction]
    exact strongCandidateHighOutput_of_fullFirst parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state _ _
      (represented.highStoredFirst parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        widthHalf widthLength state data candidate tuple)
  · rw [originalStrongWeightEquivalence_eq_reconstruction]
    exact represented.highCompactEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate tuple
  · have actual := represented.lowStoredRow parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state data candidate tuple
    have datumSame := originalStrongWeightEquivalence_eq_reconstruction parameters lower length positive
      (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
    exact actual.trans (congrArg (fun datum : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 =>
      strongLowPhysicalRHS parameters length compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state datum
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)) datumSame.symm)
  · exact boundary

end Grad.AnnularOriginalSmoothCore
