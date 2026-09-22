import AIQ1SameActualSolutionDomega

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularUniformBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularSourceGraph Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Exact reverse algebra: the full physical packet recovers the original current form. -/
theorem fullPhysicalPacket_iff_variational
    (field test : annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (boundary : HighBoundaryPrimitive parameters 0 0) :
    (inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary) =
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
        ((actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState field).val + boundary.val)) ↔
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test =
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state known auxiliary) -
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test) boundary.val := by
  constructor
  · intro packet
    simp only [actualFullHighOutput, inner_add_right] at packet
    simp only [currentHighFormValue, currentHighBulkFormValue, actualCurrentHighBoundaryFormValue]
    linear_combination -packet
  · exact actualFullHighOutput_variational parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      field test known auxiliary boundary

/-- The genuine source graph determines the candidate's complete affine outer row. -/
def candidatePhysicalOuter (data : ActualHighGraphKnownData parameters lower 0 0)
    (candidate : annularEnergySpace lower L positive) : HighBoundaryPrimitive parameters 0 0 :=
  actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState candidate +
    actualHighGraphBoundaryVector state.outerInverseState 0 0 data.datum
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs)

/-- Arbitrary compact physical weak solutions with their actual outer endpoint equal the SAME source solution. -/
theorem physicalCompactCandidate_unique
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)
    (candidate : annularEnergySpace lower L positive)
    (incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive candidate) = data.innerValue)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate data.weighted data.auxiliary))
    (outer : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num))
          (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate data.weighted data.auxiliary)
          equation mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
          (candidatePhysicalOuter parameters L compact lower positive lowerHalf lengthPositive state data candidate).val mode.val) :
    candidate = graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  apply graphDataEnergySolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data candidate incoming
  intro test
  have packet := physicalFlux_packet_converse parameters lower L positive lowerHalf lengthPositive widthHalf widthLength
    (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate data.weighted data.auxiliary)
    (candidatePhysicalOuter parameters L compact lower positive lowerHalf lengthPositive state data candidate).val equation outer test
  exact (fullPhysicalPacket_iff_variational parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    candidate test.val data.weighted data.auxiliary
    (actualHighGraphBoundaryVector state.outerInverseState 0 0 data.datum
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs))).mp packet

end Grad.AnnularPhysicalSolution
