import AIU7SameCoupledHighPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.ActualBoundaryPrimitives
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

/-- The outer high flux is formed from the final actual field and source. -/
def coupledPhysicalOuter : HighBoundaryPrimitive parameters 0 0 :=
  candidatePhysicalOuter parameters L compact lower positive lowerHalf lengthPositive state
    (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1

theorem coupledPhysicalOuter_same :
    coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData =
    graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small)
      (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) := by
  unfold coupledPhysicalOuter
  have same := congrArg (fun field : CrossHighSpace lower L positive lengthPositive => field.ofLp.1)
    (coupledKnownResponse_sameHigh parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
  rw [same]
  rfl

theorem coupledPhysicalOutput_packet
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val)
      (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val)
      (coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).val := by
  rw [coupledPhysicalOutput_same, coupledPhysicalOuter_same]
  exact graphDataPhysicalOutput_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) _ test

/-- This is the actual r=1 endpoint of the original physical flux moment. -/
theorem coupledPhysicalOutput_outerMoment (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
      (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num))
        (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
        (coupledPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) mode) =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).val mode.val :=
  physicalFluxMomentGraph_outer parameters lower L positive lowerHalf lengthPositive widthHalf widthLength _ _ _
    (coupledPhysicalOutput_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) mode

/-- The true high physical boundary equals the prescribed datum minus the
actual low boundary contribution, in the original BCT convention. -/
theorem coupledPhysicalBoundary_equation :
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
        (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 highData.graphs) =
      highData.datum + lowToHighBoundaryCross parameters lower L compact lengthPositive positive lowerHalf state
        (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2 := by
  apply (candidatePhysicalBoundary_iff parameters L compact lower positive lowerHalf lengthPositive state
    (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1
    (coupledPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)).mpr
  rfl

end Grad.AnnularFullSource
