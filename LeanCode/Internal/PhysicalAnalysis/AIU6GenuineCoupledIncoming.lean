import AIU5ActualCoupledKnownSourceResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularPhysicalSolution Grad.AnnularCoupledInverse
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularTiltedReference
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

theorem coupledKnownResponse_highIncoming :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive
        (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1) =
      highData.innerValue :=
  (coupledKnownResponse_high parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).1

theorem coupledKnownResponse_lowIncoming :
    lowIncomingTrace lower L positive (lowerHalf.trans_lt (by norm_num))
      (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2 = lowData.ofLp.2 := by
  have equation := congrArg (fun data : LowEnergyData lower => data.ofLp.2)
    (coupledKnownResponse_low parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
  change _ = lowData.ofLp.2 + 0 at equation
  exact equation.trans (add_zero _)

/-- The slope of the SAME original completed low graph is exactly the
current low row plus the two physical source contributions. -/
theorem coupledKnownResponse_lowSlope :
    let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    solution.ofLp.2.val 1 =
      lowCurrentBulk parameters L compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state (solution.ofLp.2.val 0) +
      knownLowForcing parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData.ofLp.1.ofLp.1 lowData.ofLp.1.ofLp.2 +
      highToLowBulkCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state solution.ofLp.1 := by
  have equation := congrArg (fun data : LowEnergyData lower => data.ofLp.1)
    (coupledKnownResponse_low parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
  dsimp only
  change (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2.val 1 -
    lowCurrentBulk parameters L compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state
      ((coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2.val 0) =
    knownLowForcing parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData.ofLp.1.ofLp.1 lowData.ofLp.1.ofLp.2 +
    highToLowBulkCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1 at equation
  exact (sub_eq_iff_eq_add.mp equation).trans (by abel)

end Grad.AnnularFullSource
