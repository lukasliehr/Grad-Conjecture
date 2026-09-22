import AKA5OriginalDatumTraceRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularForwardTraces
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives Grad.AnnularReconstruction Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule traceCoupledRealNormed traceCoupledRealModule

abbrev OriginalBoundaryCoordinates (parameters : PhaseParameters) :=
  WithLp 2 (HighBoundaryPrimitive parameters 0 0 × WithLp 2 (AnnularBoundary × LowEnergyBoundary))

private theorem originalBoundaryCoordinates_ext (parameters : PhaseParameters)
    (first second : OriginalBoundaryCoordinates parameters)
    (outer : first.ofLp.1 = second.ofLp.1)
    (high : first.ofLp.2.ofLp.1 = second.ofLp.2.ofLp.1)
    (low : first.ofLp.2.ofLp.2 = second.ofLp.2.ofLp.2) : first = second := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact outer
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    exact Prod.ext high low

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

/-- All original boundary data recovered from arbitrary retained and copied
source graphs, in the literal original three Hilbert norm coordinates. -/
def originalBoundaryTrace (input : OriginalTraceInput parameters length lower positive) :
    OriginalBoundaryCoordinates parameters :=
  WithLp.toLp 2 (originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input,
    WithLp.toLp 2 (originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive input.1,
      originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive input.1))

theorem originalBoundaryTrace_continuous :
    Continuous (originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state) :=
  (WithLp.prod_continuous_toLp 2 _ _).comp
    ((originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state).continuous.prodMk
      ((WithLp.prod_continuous_toLp 2 _ _).comp
        (((originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive).continuous.comp continuous_fst).prodMk
          ((originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive).continuous.comp continuous_fst))))

def originalBoundaryTraceConstant : ℝ :=
  ‖originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state‖ +
    ‖originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive‖ +
    ‖originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive‖

theorem originalBoundaryTraceConstant_nonnegative :
    0 ≤ originalBoundaryTraceConstant parameters length compact lower positive lowerHalf lengthPositive state := by
  unfold originalBoundaryTraceConstant
  exact add_nonneg (add_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)) (ContinuousLinearMap.opNorm_nonneg _)

/-- Bounded AK32 boundary observation on every fixed positive collar. No
smooth-density or forward-continuity premise is used. -/
theorem originalBoundaryTrace_bound (input : OriginalTraceInput parameters length lower positive) :
    ‖originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
      originalBoundaryTraceConstant parameters length compact lower positive lowerHalf lengthPositive state * ‖input‖ := by
  have outer := hilbert_norm_le_add (originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input)
  have inner := hilbert_norm_le_add (originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input).ofLp.2
  have high := (originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive).le_opNorm input.1
  have low := (originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive).le_opNorm input.1
  have first := norm_fst_le input
  have highBound := high.trans (mul_le_mul_of_nonneg_left first
    (norm_nonneg (originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive)))
  have lowBound := low.trans (mul_le_mul_of_nonneg_left first
    (norm_nonneg (originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive)))
  have outerBound := originalOuterBoundaryTrace_bound parameters length compact lower positive lowerHalf lengthPositive state input
  change ‖originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
    ‖originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input‖ +
      ‖(originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input).ofLp.2‖ at outer
  change ‖(originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state input).ofLp.2‖ ≤
    ‖originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive input.1‖ +
      ‖originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive input.1‖ at inner
  unfold originalBoundaryTraceConstant
  nlinarith only [outer,inner,highBound,lowBound,outerBound]

variable (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

theorem originalBoundaryTrace_response (data : OriginalStrongCarrier parameters lower 0 0) :
    originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data,
        data.val.ofLp.1.ofLp.1) = data.val.ofLp.2 := by
  apply originalBoundaryCoordinates_ext parameters
  · exact originalOuterBoundaryTrace_response parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  · exact originalHighIncomingTrace_response parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  · exact originalLowIncomingTrace_response parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data


include small in
/-- Every candidate satisfying the original sourced equation has exactly
the original full boundary datum, through the constructed bounded traces. -/
theorem originalBoundaryTrace_of_equation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (candidate,data.val.ofLp.1.ofLp.1) = data.val.ofLp.2 := by
  have same := originalSharedResponse_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data candidate equation
  exact (congrArg (fun field => originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
    (field,data.val.ofLp.1.ofLp.1)) same).trans
      (originalBoundaryTrace_response parameters length compact lower positive lowerHalf lengthPositive state widthHalf widthLength small data)


end Grad.AnnularForwardTraces
