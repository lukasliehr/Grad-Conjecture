import AIU15IndependentLowPhysicalEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularFullSource
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.AnnularTiltedReference Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

open Grad.AnnularPhysicalSolution Grad.AnnularCrossMaps Grad.AnnularOmegaGraph

open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularLowVolterra

/-- Uniqueness among arbitrary original coupled physical weak candidates,
with their genuine closed-graph derivatives, incoming traces, first-row flux,
and actual moment boundary trace. -/
theorem coupledPhysicalCandidates_unique
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)
    (candidate : CoupledSpace lower L positive lengthPositive) :
    let data := addCrossData parameters lower highData
      (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state candidate.ofLp.2)
    let field := candidate.ofLp.1.ofLp.1
    let flux := candidate.ofLp.1.ofLp.2
    let lowKnown := knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData +
      highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1
    ∀ (x : DivisionRow 1 lower)
    (_fluxValue : flux.val 0 = highFullRestriction lower x)
    (_high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → x mode = 0)
    (_incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive field) = data.innerValue)
    (_first : retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state x =
      eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, data.weighted)))
    (weak : ∀ mode : HighAnnularMode,
      CollarWeakDerivative lower
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
        (physicalFluxOrdinarySlope parameters lower L positive
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
    (outerX : HighBoundaryPrimitive parameters 0 0)
    (_physicalBoundary : graphNativePhysicalBoundary state.outerInverseState 0 0 outerX
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 field)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum)
    (_outer : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num))
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x)
          (compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
            lengthPositive widthHalf widthLength _ weak) mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • outerX.val mode.val)
    (_lowIncoming : lowIncomingTrace lower L positive (lowerHalf.trans_lt (by norm_num)) candidate.ofLp.2 = lowKnown.ofLp.2)
    (_lowEquation : ∀ index : LowAnnularIndex,
      collarScalar 1 lower (lowMuInverseCurve lower L positive index.2.val.2)
        (lowEnergyDerivative lower L positive index candidate.ofLp.2.val) =
      lowCurrentGeneratorValue parameters L compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.2 index +
        lowDataResidual lower positive lowKnown index),
    candidate = coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData := by
  dsimp only
  intro x fluxValue high incoming first weak outerX physicalBoundary outer lowIncoming lowEquation
  have highEquation := independentHighPhysicalSource_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small)
    (addCrossData parameters lower highData
      (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state candidate.ofLp.2))
    candidate.ofLp.1.ofLp.1 x candidate.ofLp.1.ofLp.2 fluxValue high incoming first weak outerX physicalBoundary outer
  have lowForward := (independentLowPhysicalSource_iff parameters L compact lower positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData +
      highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1)
    candidate.ofLp.2).mpr ⟨lowIncoming, lowEquation⟩
  exact coupledKnownResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    highData lowData candidate highEquation lowForward

end Grad.AnnularFullSource
