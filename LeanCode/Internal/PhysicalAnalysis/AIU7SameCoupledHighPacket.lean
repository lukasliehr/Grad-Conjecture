import AIU6GenuineCoupledIncoming

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
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

def coupledHighData : ActualHighGraphKnownData parameters lower 0 0 :=
  addCrossData parameters lower highData (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2)

theorem coupledKnownResponse_sameHigh :
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1 =
    fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small)
      (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) :=
  (highSourceEquation_iff_response parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) _ _).mp
    (coupledKnownResponse_high parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)

/-- The actual coupled high three-output packet, using the final high field
and the actual source produced by the final low field. -/
def coupledPhysicalOutput : DivisionRow 3 lower :=
  actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1
    (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).weighted
    (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).auxiliary

theorem coupledPhysicalOutput_same :
    coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData =
    graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small)
      (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) := by
  unfold coupledPhysicalOutput
  have same := congrArg (fun field : CrossHighSpace lower L positive lengthPositive => field.ofLp.1)
    (coupledKnownResponse_sameHigh parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)
  rw [same]
  rfl

theorem coupledPhysicalOutput_compact :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength
      (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) := by
  rw [coupledPhysicalOutput_same]
  exact graphDataPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) _

end Grad.AnnularFullSource
