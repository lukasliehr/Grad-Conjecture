import AKP1ActualRestrictedEquationAndCompactness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularCrossOrbit
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

/-- The already accepted context, at a new collar and the SAME fixed state. -/
def fixedExhaustionContext (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    CoupledCoordinateContext parameters length compact :=
  ⟨(lower,state), positive,lowerHalf,lengthPositive,widthHalf,widthLength,small⟩

/-- Exactly AKL's existing zero-independent-boundary inverse. -/
def fixedExhaustionSolve (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    OriginalFiveBlockAmbient parameters lower length positive :=
  originalExhaustionSolve parameters length compact
    (fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf) data

theorem fixedExhaustionSolve_sources (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    (fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf data).ofLp.2 =
      data.val.ofLp.1 := rfl

theorem fixedExhaustionSolve_equation (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf data ∈
      OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state := by
  refine ⟨(zeroBoundaryDatum parameters lower data,
    (fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf data).ofLp.1), ?_, rfl⟩
  exact originalExhaustionSolve_equation parameters length compact
    (fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf) data

theorem fixedExhaustionSolve_fullOuter (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    let solution := fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf data
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (solution.ofLp.1,solution.ofLp.2.ofLp.1) = 0 := by
  have boundary := originalExhaustionSolve_boundary parameters length compact
    (fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf) data
  exact congrArg (fun packet : OriginalBoundaryCoordinates parameters => packet.ofLp.1) boundary

/-- The original single-collar solve already has the required native
retained estimate. Uniformity is inherited from the accepted BF inverse. -/
theorem fixedExhaustionSolve_retainedBound (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    originalWeightedRetainedNorm parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf data).ofLp.1 ≤
    2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact *
      originalWeightedDatumNorm parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
        (zeroBoundaryDatum parameters lower data) :=
  originalSharedResponse_uniform_base parameters length compact
    (fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small lower positive lowerHalf)
    (zeroBoundaryDatum parameters lower data)

end Grad.ActualAnnularExhaustion
