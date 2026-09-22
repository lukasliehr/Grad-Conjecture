import AIU8ActualCoupledPhysicalBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

/-- The final coupled high flux obeys the original ordinary distributional row. -/
theorem coupledPhysicalOutput_ordinaryWeak (mode : HighAnnularMode) :
    CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
        (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) mode))
      (physicalFluxOrdinarySlope parameters lower L positive
        (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) mode) :=
  (compactPhysicalPacketEquation_iff_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive widthHalf widthLength _).mp
    (coupledPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) mode

/-- Exact original low datum after evaluating the final high cross source. -/
def coupledLowData : LowEnergyData lower :=
  knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state lowData +
    highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1

theorem coupledKnownResponse_sameLow :
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2 =
      lowCurrentInverse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
        (coupledLowData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) := by
  have identity := lowCurrentInverse_dataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
    (coupledPrimitive_lowSmall parameters L compact state small)
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2
  rw [coupledKnownResponse_low] at identity
  exact identity.symm

/-- The derivative of the SAME low graph is the genuine BE normalized weak
row for the full known and high cross source. -/
theorem coupledKnownResponse_lowNormalizedEquation (index : LowAnnularIndex) :
    collarScalar 1 lower (lowMuInverseCurve lower L positive index.2.val.2)
      (lowEnergyDerivative lower L positive index
        (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2.val) =
    lowCurrentGeneratorValue parameters L compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.2 index +
    lowDataResidual lower positive
      (coupledLowData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) index := by
  rw [coupledKnownResponse_sameLow]
  exact lowCurrentInverse_normalizedEquation parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
    (coupledPrimitive_lowSmall parameters L compact state small) _ index

end Grad.AnnularFullSource
