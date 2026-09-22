import AJC11SameFullPhysicalPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentEnergy Grad.AnnularFullSource Grad.AnnularStrongData Grad.AnnularKnownLow
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.ActualBoundaryPrimitives
open Grad.AnnularPhysicalSolution
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation

private theorem recoverFullBoundary {E : Type*} [AddCommGroup E]
    (high low datum : E) (equation : high = datum + -low) : high + low = datum := by
  rw [equation]
  abel

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)

/-- The genuine full physical boundary is exactly the independently prescribed
outer datum. The source graphs occur once in the high graph-native term;
the low term is the original physical seven-trace boundary, with its true sign. -/
theorem sharedStrongResponse_fullBoundary
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let highData := strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData
        (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data))
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 solution.ofLp.1.ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 highData.graphs) +
      lowStateBoundaryPR parameters L compact state
        (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf solution.ofLp.2) = highData.datum := by
  exact recoverFullBoundary _ _ _
    (coupledPhysicalBoundary_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data))

end Grad.AnnularStrongSolution
