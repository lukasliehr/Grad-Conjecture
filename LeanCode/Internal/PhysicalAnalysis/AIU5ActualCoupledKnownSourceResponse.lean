import AIU4ActualHighSourceEquation
import AIT99OriginalCoupledInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- The two actual diagonal responses to prescribed physical sources. -/
def knownDiagonalResponse (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower) :
    CoupledSpace lower L positive lengthPositive :=
  WithLp.toLp 2 (fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) highData,
    knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state lowData)

/-- The actual complete coupled response, built from both physical diagonal
solvers and the convergent series on the same original graph. -/
def coupledKnownResponse (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower) :
    CoupledSpace lower L positive lengthPositive :=
  actualCoupledInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small
    (knownDiagonalResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)

/-- The high component solves the exact full known source plus the literal
low-to-high source; its source graph and incoming trace are unchanged. -/
theorem coupledKnownResponse_high (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower) :
    let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (addCrossData parameters lower highData (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state solution.ofLp.2))
      solution.ofLp.1 := by
  dsimp only
  apply (highSourceEquation_iff_response parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) _ _).mpr
  rw [fullKnownHighResponse_addCross]
  exact (actualCoupledInverse_coordinates parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small
    (knownDiagonalResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)).1

/-- The original low Cauchy equation includes the same prescribed source
and the actual high-to-low cross source exactly once. -/
theorem coupledKnownResponse_low (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower) :
    let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state solution.ofLp.2 =
      knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData +
      highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state solution.ofLp.1 := by
  have equation := actualCoupledInverse_lowResidual parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small
    (knownDiagonalResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
  dsimp only at equation ⊢
  change lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2 =
    lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state lowData) + _ at equation
  rw [knownLowResponse_equation parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
    (coupledPrimitive_lowSmall parameters L compact state small)] at equation
  exact equation

/-- Uniqueness among arbitrary original high/low graph candidates for the
same full sourced equations. -/
theorem coupledKnownResponse_unique (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)
    (candidate : CoupledSpace lower L positive lengthPositive)
    (high : HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (addCrossData parameters lower highData (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state candidate.ofLp.2)) candidate.ofLp.1)
    (low : lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state candidate.ofLp.2 =
      knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData +
      highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1) :
    candidate = coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData := by
  have highFixed := (highSourceEquation_iff_response parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) _ _).mp high
  rw [fullKnownHighResponse_addCross] at highFixed
  apply actualCoupledInverse_residual_unique parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small
    (knownDiagonalResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) candidate highFixed
  change _ = lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state lowData) + _
  rw [knownLowResponse_equation parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
    (coupledPrimitive_lowSmall parameters L compact state small)]
  exact low

end Grad.AnnularFullSource
