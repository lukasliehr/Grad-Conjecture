import AID15ExactCompletedPhysicalConsumer
import AIE6FullPhysicalOutputBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularUniformBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)

/-- The three literal physical outputs belonging to the SAME current source solution. -/
def graphDataPhysicalOutput : DivisionRow 3 lower :=
  actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    data.weighted data.auxiliary

/-- The affine original outer datum, using the actual source graph trace. -/
def graphDataPhysicalOuter : HighBoundaryPrimitive parameters 0 0 :=
  actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState
    (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) +
  actualHighGraphBoundaryVector state.outerInverseState 0 0 data.datum
    (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs)

theorem graphDataPhysicalOutput_packet
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val)
      (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val)
      (graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).val :=
  graphDataEnergySolution_full_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data test

theorem graphDataPhysicalOutput_compact :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength
      (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) :=
  compactPhysicalPacketEquation_of_testLaw parameters lower L positive lowerHalf lengthPositive widthHalf widthLength _
    (graphDataEnergySolution_zeroOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)

/-- The recovered flux is in the actual original closed Domega graph. -/
def graphDataPhysicalFlux : annularOmegaGraph lower L positive lengthPositive :=
  physicalFluxGraph parameters lower L positive lengthPositive widthHalf widthLength (lowerHalf.trans_lt (by norm_num))
    (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (graphDataPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)

theorem graphDataPhysicalFlux_value :
    (graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).val 0 =
      highPhysicalOutput lower 0
        (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := rfl

/-- Radius-independent original Domega bound in exactly the given coherent BF2 data. -/
theorem graphDataPhysicalFlux_bound :
    ‖graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      4 * (eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|) *
        (32 * data.functionalSize parameters L compact lower state 0 0 +
          322 * uniformInnerLiftConstant L * ‖data.innerValue‖) +
        4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖data.weighted‖ + 3 * ‖data.auxiliary‖) := by
  apply (physicalFluxGraph_bound parameters lower L positive lengthPositive widthHalf widthLength
    (lowerHalf.trans_lt (by norm_num)) _ _).trans
  exact mul_le_mul_of_nonneg_left
    (graphDataEnergySolution_fullOutput_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (by norm_num)

/-- The same graph has the actual affine physical outer endpoint, not an independent trace coordinate. -/
theorem graphDataPhysicalFlux_outer (mode : HighAnnularMode) :
    Grad.AnnularSourceGraph.weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
      (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num))
        (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        (graphDataPhysicalOutput_compact parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) mode) =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).val mode.val :=
  physicalFluxMomentGraph_outer parameters lower L positive lowerHalf lengthPositive widthHalf widthLength _ _ _
    (graphDataPhysicalOutput_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) mode

end Grad.AnnularPhysicalSolution
