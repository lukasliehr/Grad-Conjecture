import AKI38LiteralCoreSourceRecovery
import AKJ2OriginalFiveBlockClosedEquationGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularSourceGraph
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph
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

/-- Every faithfully represented literal four-field tuple is an observation
of the ORIGINAL equation, with its own computed source and boundary datum.
The core predicate itself contains neither an equation nor an inverse. -/
theorem coreAnn_subset_originalObservedEquationGraph :
    CoreAnn parameters length compact lower positive domain lengthPositive state ⊆
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state := by
  rintro point ⟨tuple,represented⟩
  let lowerHalf : lower ≤ 1/2 := domain.trans (min_le_left _ _)
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let datum := originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state point
  have same : originalFiveBlockObservation parameters lower length positive (datum,point.ofLp.1) = point :=
    represented.forwardObservation parameters length compact lower positive bounded lengthPositive state tuple point lowerHalf
  have tupleSame : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (datum,point.ofLp.1)) := same.symm ▸ represented
  have graphs : datum.val.ofLp.1.ofLp.1 = point.ofLp.2.ofLp.1 :=
    congrArg (fun value : OriginalFiveBlockAmbient parameters lower length positive => value.ofLp.2.ofLp.1) same
  have boundary : originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (point.ofLp.1,datum.val.ofLp.1.ofLp.1) = datum.val.ofLp.2 := by
    rw [graphs]
    exact (originalForwardDatum_boundary parameters length compact lower positive lowerHalf lengthPositive state point).symm
  exact ⟨(datum,point.ofLp.1),
    tupleSame.originalEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      datum point.ofLp.1 tuple boundary,same⟩

/-- Closure in precisely AK31's five norms preserves the genuine original
variational equation and the bounded canonical datum recovery. -/
theorem coreAnnClosure_subset_originalObservedEquationGraph :
    CoreAnnClosure parameters length compact lower positive domain lengthPositive state ⊆
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state :=
  closure_minimal (coreAnn_subset_originalObservedEquationGraph parameters length compact lower positive domain lengthPositive
    widthHalf widthLength state small)
    (originalObservedEquationGraph_closed parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state small)

end Grad.AnnularOriginalSmoothCore
