import AIU10FullHighSingleDataNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowVolterra
open Grad.GaugeCoefficients.Physical.Allocation

private theorem hilbertPairFstBound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data.ofLp.1‖ ≤ ‖data‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith only [square, norm_nonneg data, norm_nonneg data.ofLp.1, sq_nonneg ‖data.ofLp.2‖]

private theorem hilbertPairSndBound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data.ofLp.2‖ ≤ ‖data‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith only [square, norm_nonneg data, norm_nonneg data.ofLp.2, sq_nonneg ‖data.ofLp.1‖]

private theorem hilbertPairTriangle {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data‖ ≤ ‖data.ofLp.1‖ + ‖data.ofLp.2‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith only [square, norm_nonneg data, norm_nonneg data.ofLp.1, norm_nonneg data.ofLp.2,
    mul_nonneg (norm_nonneg data.ofLp.1) (norm_nonneg data.ofLp.2)]

private theorem hilbertPairInverseBound {E F G H : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedAddCommGroup H]
    (high : E → G) (low : F → H)
    (inverse : WithLp 2 (G × H) → WithLp 2 (G × H))
    (highConstant lowConstant : ℝ)
    (highNonnegative : 0 ≤ highConstant) (lowNonnegative : 0 ≤ lowConstant)
    (highBound : ∀ field, ‖high field‖ ≤ highConstant * ‖field‖)
    (lowBound : ∀ field, ‖low field‖ ≤ lowConstant * ‖field‖)
    (inverseBound : ∀ field, ‖inverse field‖ ≤ 2 * ‖field‖)
    (data : WithLp 2 (E × F)) :
    ‖inverse (WithLp.toLp 2 (high data.ofLp.1, low data.ofLp.2))‖ ≤
      2 * (highConstant + lowConstant) * ‖data‖ := by
  have first := (highBound data.ofLp.1).trans
    (mul_le_mul_of_nonneg_left (hilbertPairFstBound data) highNonnegative)
  have second := (lowBound data.ofLp.2).trans
    (mul_le_mul_of_nonneg_left (hilbertPairSndBound data) lowNonnegative)
  apply (inverseBound _).trans
  calc
    2 * ‖WithLp.toLp 2 (high data.ofLp.1, low data.ofLp.2)‖ ≤
        2 * (‖high data.ofLp.1‖ + ‖low data.ofLp.2‖) :=
      mul_le_mul_of_nonneg_left (hilbertPairTriangle _) (by norm_num)
    _ ≤ 2 * (highConstant * ‖data‖ + lowConstant * ‖data‖) :=
      mul_le_mul_of_nonneg_left (add_le_add first second) (by norm_num)
    _ = _ := by ring

private theorem operatorBoundFromNorm {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (operator : E →L[𝕜] F) (constant : ℝ) (bound : ‖operator‖ ≤ constant) (field : E) :
    ‖operator field‖ ≤ constant * ‖field‖ :=
  (operator.le_opNorm field).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg field))

/-- Complete independent high/low source pair. The original strong datum
will embed by using one shared source tuple in its two projections. -/
abbrev IndependentCoupledData (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :=
  WithLp 2 (ActualHighKnownCarrier parameters lower positive bounded 0 0 × KnownLowData lower)

def knownLowResponseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  2 * Real.sqrt (lowReferenceGraphConstant parameters L) *
    (2 * knownLowSourceConstant parameters L compact + lowBalanceConstant L parameters.gamma + 5)

theorem knownLowResponseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ knownLowResponseConstant parameters L compact := by
  have coefficient := knownLowSourceConstant_nonnegative parameters L compact
  have balance : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
  unfold knownLowResponseConstant
  positivity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- The actual coupled response on the complete independently prescribed data. -/
def independentCoupledResponse
    (data : IndependentCoupledData parameters lower positive (lowerHalf.trans (by norm_num))) :
    CoupledSpace lower L positive lengthPositive :=
  coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data.ofLp.1) data.ofLp.2

/-- Exactly the factor two from the actual coupling series, followed by the
single Hilbert norm of the two independent data carriers. -/
theorem independentCoupledResponse_bound
    (data : IndependentCoupledData parameters lower positive (lowerHalf.trans (by norm_num))) :
    let response : CoupledSpace lower L positive lengthPositive :=
      independentCoupledResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    ‖response‖ ≤
      2 * (fullKnownHighNormConstant parameters L compact state + knownLowResponseConstant parameters L compact) * ‖data‖ := by
  exact hilbertPairInverseBound
    (fun high : ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 =>
      fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (coupledPrimitive_highSmall parameters L compact state small)
        (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 high))
    (knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state)
    (actualCoupledInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
    (fullKnownHighNormConstant parameters L compact state) (knownLowResponseConstant parameters L compact)
    (fullKnownHighNormConstant_nonnegative parameters L compact state)
    (knownLowResponseConstant_nonnegative parameters L compact)
    (fullKnownHighResponse_singleNorm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small))
    (operatorBoundFromNorm
      (knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state)
      (knownLowResponseConstant parameters L compact)
      (knownLowResponse_uniform parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
        (coupledPrimitive_lowSmall parameters L compact state small) (coupledPrimitive_budget_one parameters L compact state small)))
    (actualCoupledInverse_apply_bound parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
    data

end Grad.AnnularFullSource
