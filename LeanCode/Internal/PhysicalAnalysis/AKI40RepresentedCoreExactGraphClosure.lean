import AKI39LiteralCoreOriginalEquationImage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularSourceGraph
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph Grad.AnnularSolvedGraphDensity
open Grad.AnnularStrongOrbit Grad.AnnularForwardDatum Grad.AnnularForwardTraces
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (domain : lower ≤ min (1/2) length) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include small

/-- Every actual original datum's SAME response is approximable by literal
represented four-field tuples in precisely the five original graph norms. -/
theorem originalResponse_mem_representedCoreClosure (data : OriginalStrongCarrier parameters lower 0 0) :
    originalFiveBlockObservation parameters lower length positive
      (data,originalSharedResponse parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state small data) ∈
      CoreAnnClosure parameters length compact lower positive domain lengthPositive state :=
  originalSolvedGraph_closed_transfer parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
    widthHalf widthLength state small
    (originalFiveBlockObservation parameters lower length positive)
    (originalFiveBlockObservation_continuous parameters lower length positive)
    (CoreAnnClosure parameters length compact lower positive domain lengthPositive state)
    (coreAnnClosure_closed parameters length compact lower positive domain lengthPositive state)
    (fun core => originalSmoothResponse_coreAnnClosure parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state small core domain) data

/-- Exact closure of the faithfully represented literal four-field core.
This does not assert total graph realization for every admissible tuple. -/
theorem representedCoreClosure_eq_originalObservedEquationGraph :
    CoreAnnClosure parameters length compact lower positive domain lengthPositive state =
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state := by
  apply Set.Subset.antisymm
  · exact coreAnnClosure_subset_originalObservedEquationGraph parameters length compact lower positive domain lengthPositive
      widthHalf widthLength state small
  · rintro point ⟨pair,equation,rfl⟩
    have same := originalSharedResponse_unique parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state small pair.1 pair.2 equation
    change originalFiveBlockObservation parameters lower length positive (pair.1,pair.2) ∈
      CoreAnnClosure parameters length compact lower positive domain lengthPositive state
    rw [same]
    exact originalResponse_mem_representedCoreClosure parameters length compact lower positive domain lengthPositive
      widthHalf widthLength state small pair.1

/-- Exact bounded datum recovery on this completed represented core. -/
theorem representedCoreClosure_recovery (point : OriginalFiveBlockAmbient parameters lower length positive)
    (inside : point ∈ CoreAnnClosure parameters length compact lower positive domain lengthPositive state) :
    let pair := originalForwardPair parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive state point
    OriginalStrongCoupledEquation parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state pair.1 pair.2 ∧
      originalFiveBlockObservation parameters lower length positive pair = point :=
  originalObservedEquationGraph_recovery parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
    widthHalf widthLength state small point
    (coreAnnClosure_subset_originalObservedEquationGraph parameters length compact lower positive domain lengthPositive
      widthHalf widthLength state small inside)

end Grad.AnnularOriginalSmoothCore
