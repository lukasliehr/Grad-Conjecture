import AKJ1ClosedObservedGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularFullGraph
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularSolvedGraphDensity
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)

/-- Exactly the five original observations of genuine complete equation
pairs. This set does not assert the still separate literal smooth-core closure. -/
def OriginalObservedEquationGraph : Set (OriginalFiveBlockAmbient parameters lower length positive) :=
  (originalFiveBlockObservation parameters lower length positive) ''
    {pair : OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive |
      OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state pair.1 pair.2}

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
include small

theorem originalObservedEquationGraph_closed :
    IsClosed (OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state) := by
  apply closedObservedGraph
    (originalFiveBlockObservation parameters lower length positive)
    (Grad.AnnularForwardDatum.originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state)
    (originalFiveBlockObservation_continuous parameters lower length positive)
    (Grad.AnnularForwardDatum.originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state).continuous
  · rw [← originalSolvedEquationGraph_closure parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small]
    exact isClosed_closure
  · intro pair equation
    exact Grad.AnnularForwardDatum.originalForwardPair_of_equation parameters length compact lower positive lowerHalf lengthPositive state
      widthHalf widthLength small pair.1 pair.2 equation

theorem originalObservedEquationGraph_recovery
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (inside : point ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state) :
    let pair := Grad.AnnularForwardDatum.originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state point
    OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state pair.1 pair.2 ∧
      originalFiveBlockObservation parameters lower length positive pair = point := by
  obtain ⟨pair,equation,rfl⟩ := inside
  have same := Grad.AnnularForwardDatum.originalForwardPair_of_equation parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small pair.1 pair.2 equation
  change Grad.AnnularForwardDatum.originalForwardPair parameters length compact lower positive lowerHalf lengthPositive state
    (originalFiveBlockObservation parameters lower length positive pair) = pair at same
  dsimp only
  rw [same]
  exact ⟨equation,rfl⟩

theorem originalObservedEquationGraph_eq_range :
    OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state =
      range (Grad.AnnularForwardDatum.originalSolvedFiveBlock parameters length compact lower positive lowerHalf lengthPositive state
        widthHalf widthLength small) := by
  ext point
  constructor
  · rintro ⟨pair,equation,rfl⟩
    refine ⟨pair.1,?_⟩
    have unique := originalSharedResponse_unique parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small pair.1 pair.2 equation
    exact congrArg (fun candidate => originalFiveBlockObservation parameters lower length positive (pair.1,candidate)) unique.symm
  · rintro ⟨data,rfl⟩
    exact ⟨(data,originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data),
      originalSharedResponse_equation parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data,rfl⟩

end Grad.AnnularFullGraph
