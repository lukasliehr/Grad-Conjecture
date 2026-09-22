import AKE3ExactOriginalEquationDataRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularForwardDatum
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.ActualBoundaryPrimitives Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

/-- Recover the full original datum together with the SAME retained candidate. -/
def originalForwardPair : ForwardFiveBlocks parameters lower length positive →L[ℝ]
    (OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive) :=
  (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state).prod forwardHilbertFirst

theorem originalForwardPair_apply (field : ForwardFiveBlocks parameters lower length positive) :
    originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state field =
      (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state field,field.ofLp.1) := rfl

variable (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

include small in
theorem originalForwardPair_of_equation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state
      (originalFiveBlockObservation parameters lower length positive data candidate) = (data,candidate) :=
  Prod.ext (originalForwardDatum_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small data candidate equation) rfl

include small in
/-- Five original graph blocks distinguish arbitrary pairs satisfying the
original equation, because the constructed bounded forward map recovers the full datum. -/
theorem originalFiveBlockObservation_injective_on_equation :
    Set.InjOn (fun pair : OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive =>
      originalFiveBlockObservation parameters lower length positive pair.1 pair.2)
      {pair | OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state pair.1 pair.2} := by
  intro first firstEquation second secondEquation same
  have firstRecovery := originalForwardPair_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small first.1 first.2 firstEquation
  have secondRecovery := originalForwardPair_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small second.1 second.2 secondEquation
  exact firstRecovery.symm.trans ((congrArg
    (originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state) same).trans secondRecovery)

/-- The original five measured graph blocks of the SAME independently prescribed response. -/
def originalSolvedFiveBlock (data : OriginalStrongCarrier parameters lower 0 0) :
    ForwardFiveBlocks parameters lower length positive :=
  originalFiveBlockObservation parameters lower length positive data
    (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)

theorem originalForwardDatum_leftInverse :
    Function.LeftInverse (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state)
      (originalSolvedFiveBlock parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small) :=
  originalForwardDatum_response parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small

theorem originalSolvedFiveBlock_injective :
    Function.Injective (originalSolvedFiveBlock parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small) :=
  (originalForwardDatum_leftInverse parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small).injective

include widthHalf widthLength small in
theorem originalForwardDatum_surjective :
    Function.Surjective (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state) :=
  (originalForwardDatum_leftInverse parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small).surjective

include small in
/-- The exact original full datum norm is controlled by the five original
graph blocks on every equation point, with the explicit fixed-collar trace bound. -/
theorem originalDatum_bound_by_fiveBlocks (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    ‖data‖ ≤ originalForwardDatumConstant parameters length compact lower positive lowerHalf lengthPositive state *
      ‖originalFiveBlockObservation parameters lower length positive data candidate‖ := by
  have bound := originalForwardDatum_bound parameters length compact lower positive lowerHalf lengthPositive state
    (originalFiveBlockObservation parameters lower length positive data candidate)
  rwa [originalForwardDatum_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small data candidate equation] at bound

end Grad.AnnularForwardDatum
