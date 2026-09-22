import AJC13FullPhysicalBoundary
import AJC15SameFullHighFirstRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution Grad.AnnularCurrentGreen
open Grad.AnnularTiltedReference Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularLowReference
open Grad.AnnularReconstruction Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCoupledInverse
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

theorem sharedStrongResponse_highIncoming :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1.ofLp.1) =
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data).innerValue :=
  coupledKnownResponse_highIncoming parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)

theorem sharedStrongResponse_lowIncoming :
    lowIncomingTrace lower L positive (lowerHalf.trans_lt (by norm_num))
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.2 =
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.2 :=
  coupledKnownResponse_lowIncoming parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)

/-- Original compact flux equation on the single full physical reconstruction. -/
theorem sharedStrongResponse_fullCompact :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength
      (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) := by
  rw [← sharedStrongPhysicalOutput_sameFull parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data]
  exact coupledPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)

/-- The weak derivative belongs to the original radial graph; it is not
created by assigning a value to a missing derivative coordinate. -/
theorem sharedStrongResponse_fullOrdinaryWeak (mode : HighAnnularMode) :
    let packet := fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode))
      (physicalFluxOrdinarySlope parameters lower L positive packet mode) := by
  exact (compactPhysicalPacketEquation_iff_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive widthHalf widthLength _).mp
      (sharedStrongResponse_fullCompact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) mode

/-- Genuine original low normalized derivative of the same full physical row. -/
theorem sharedStrongResponse_fullLowNormalized (index : LowAnnularIndex) :
    let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    collarScalar 1 lower (lowMuInverseCurve lower L positive index.2.val.2)
      (lowEnergyDerivative lower L positive index solution.ofLp.2.val) =
    collarScalar 1 lower (lowStorageInverse lower positive)
      (strongLowPhysicalRHS parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state data solution index) := by
  dsimp only
  rw [lowEnergy_normalized_derivative]
  exact congrArg (fun field : LowEnergyBulk lower => collarScalar 1 lower (lowStorageInverse lower positive) (field index))
    (sharedStrongResponse_fullLowRow parameters L compact lower positive lengthPositive state lowerHalf widthHalf widthLength small data)

end Grad.AnnularStrongSolution
