import AKI32ArbitraryHighElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularCurrentSolution
open Grad.AnnularPhysicalSolution Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCrossMaps Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularCurrentGreen
open Grad.AnnularFullSource Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularStrongSolution Grad.AnnularRestriction

private theorem fullPacketFromSplit {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (i0 i1 i2 : F →L[ℂ] G) (Q R : F →L[ℂ] F) (C V : E →L[ℂ] F)
    (x : F) (h l k : E) (g : F)
    (radius : R (Q g) = Q (R g)) :
    (i0 x + i1 (Q (C (h + k))) + i2 (Q (V (h + k)))) +
      (i1 (Q (C l)) + i2 (Q (V l) - R (Q g))) =
    i0 x + i1 (Q (C (h + l + k))) + i2 (Q (V (h + l + k) - R g)) := by
  rw [radius]
  simp only [map_add, map_sub]
  abel

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The arbitrary candidate's full first physical row identifies all three
coordinates of its actual completed high output with the literal full packet. -/
theorem strongCandidateHighOutput_of_fullFirst
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower L positive lengthPositive)
    (first : highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength solution.ofLp.1.ofLp.1 =
      highFullRestriction lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) +
        highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data))) :
    strongCandidateHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution =
      fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data solution := by
  let corrected : ActualHighGraphKnownData parameters lower 0 0 :=
    strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2
  let input : DivisionRow 8 lower := fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength
    (solution.ofLp.1.ofLp.1, corrected.weighted)
  let h : DivisionRow 7 lower := highCrossSevenInput lower L positive lengthPositive solution.ofLp.1
  let l : DivisionRow 7 lower := lowNormalizedSevenInput parameters lower L lengthPositive positive (solution.ofLp.2.val 0)
  let k : DivisionRow 7 lower := knownLowSevenPacket lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let g : DivisionRow 1 lower := (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2
  let x : DivisionRow 1 lower := highBulkIntoFull lower (crossHighX lower L positive lengthPositive solution.ofLp.1)
  let C : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower := lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
  let V : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower := lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
  let Q : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower := highRowProjection lower
  let R : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower := radialRadiusRow lower positive
  have sameX : eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input = x :=
    (strongCandidate_eliminated_of_fullFirst parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution first).symm
  have sameSeven : eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input = h + k := by
    rw [eliminatedSevenBulkAction_assembled,sameX]
    exact (assembledSevenBulk_high parameters lower positive (lowerHalf.trans (by norm_num)) L lengthPositive widthHalf widthLength
      solution.ofLp.1 corrected.weighted).trans
      (congrArg (fun packet : DivisionRow 7 lower => h + packet)
        (strongCorrectedHighData_sourcePacket parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2))
  have sameC : normalizedCBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 = Q.comp C :=
    normalizedCBulkAction_sameFullRow parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
  have sameV : normalizedRVBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 = Q.comp V :=
    normalizedRVBulkAction_sameFullRow parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
  have auxG : corrected.auxiliary 0 = Q g := strongCorrectedHighData_g parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2
  have auxC : corrected.auxiliary 1 = Q (C l) := strongCorrectedHighData_c parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2
  have auxV : corrected.auxiliary 2 = Q (V l) := strongCorrectedHighData_v parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2
  have packet := actualFullHighOutput_sameSeven parameters L compact lower positive state lowerHalf lengthPositive widthHalf widthLength
    solution.ofLp.1.ofLp.1 corrected.weighted corrected.auxiliary
  change actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    solution.ofLp.1.ofLp.1 corrected.weighted corrected.auxiliary = _
  apply packet.trans
  change (bulkMatrixUnit lower (0 : Fin 3) 0 (eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input) +
    bulkMatrixUnit lower (1 : Fin 3) 0 (normalizedCBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input)) +
    bulkMatrixUnit lower (2 : Fin 3) 0 (normalizedRVBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input))) +
    (bulkMatrixUnit lower (1 : Fin 3) 0 (corrected.auxiliary 1) + bulkMatrixUnit lower (2 : Fin 3) 0 (corrected.auxiliary 2 - R (corrected.auxiliary 0))) = _
  rw [sameX, sameSeven, sameC, sameV, auxG, auxC, auxV]
  exact fullPacketFromSplit (bulkMatrixUnit lower (0 : Fin 3) 0) (bulkMatrixUnit lower (1 : Fin 3) 0)
    (bulkMatrixUnit lower (2 : Fin 3) 0) Q R C V x h l k g (highRowProjection_radius lower positive g).symm

end Grad.AnnularOriginalSmoothCore
