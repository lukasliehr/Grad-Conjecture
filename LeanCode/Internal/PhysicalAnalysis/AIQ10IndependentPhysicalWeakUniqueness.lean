import AIQ9CompletedPhysicalFluxAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.AnnularTiltedReference Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Literal independently supplied x, actual c/rV of its seven inputs, and every direct source. -/
def independentPhysicalBulk (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : annularEnergySpace lower L positive) (x : DivisionRow 1 lower) : DivisionRow 3 lower :=
  assembledPhysicalBulk parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 x
    (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, data.weighted)) +
    directKnownThreePacket lower positive data.auxiliary

theorem independentPhysicalBulk_eq_full (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : annularEnergySpace lower L positive) (x : DivisionRow 1 lower)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → x mode = 0)
    (first : retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state x =
      eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, data.weighted))) :
    independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x =
      actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field data.weighted data.auxiliary := by
  have solved := (completedFirstRow_iff_eliminated parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 x _ high).mp first
  rw [independentPhysicalBulk, solved, ← eliminatedBulkAction_assembled, actualFullHighOutput_one_packet]

/-- Arbitrary original weak candidates satisfy uniqueness after the actual first-row, Green and boundary equivalences. -/
theorem independentPhysicalWeak_unique
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : annularEnergySpace lower L positive) (x : DivisionRow 1 lower)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → x mode = 0)
    (incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive field) = data.innerValue)
    (first : retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state x =
      eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, data.weighted)))
    (weak : ∀ mode : HighAnnularMode,
      CollarWeakDerivative lower
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
        (physicalFluxOrdinarySlope parameters lower L positive
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
    (outerX : HighBoundaryPrimitive parameters 0 0)
    (physicalBoundary : graphNativePhysicalBoundary state.outerInverseState 0 0 outerX
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 field)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum)
    (outer : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num))
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x)
          (compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
            lengthPositive widthHalf widthLength _ weak) mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • outerX.val mode.val) :
    field = graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data ∧
      x = bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
        (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  have same := independentPhysicalBulk_eq_full parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x high first
  have compactEquation := compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive widthHalf widthLength _ weak
  rw [same] at compactEquation
  have graphCongr (a b : DivisionRow 3 lower)
      (ha : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength a)
      (hb : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength b)
      (equal : a = b) (mode : HighAnnularMode) :
      physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num)) a ha mode =
      physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num)) b hb mode := by
    cases equal
    rfl
  have affine := (candidatePhysicalBoundary_iff parameters L compact lower positive lowerHalf lengthPositive state data field outerX).mp physicalBoundary
  have outerLaw (mode : HighAnnularMode) :
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num))
          (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field data.weighted data.auxiliary)
          compactEquation mode) =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (candidatePhysicalOuter parameters L compact lower positive lowerHalf lengthPositive state data field).val mode.val := by
    have traces := congrArg (weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1)
      (graphCongr _ _ (compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
        lengthPositive widthHalf widthLength _ weak) compactEquation same mode)
    exact (traces.symm.trans (outer mode)).trans
      (congrArg (fun datum : HighBoundaryPrimitive parameters 0 0 =>
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • datum.val mode.val) affine)
  have unique := physicalCompactCandidate_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    small data field incoming compactEquation outerLaw
  refine ⟨unique, ?_⟩
  have solved := (completedFirstRow_iff_eliminated parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 x _ high).mp first
  rw [unique] at solved
  exact solved.trans (actualFullHighOutput_first parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    data.weighted data.auxiliary).symm

end Grad.AnnularPhysicalSolution
