import AKI31CompletedFirstRowReverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution Grad.AnnularCurrentGreen
open Grad.AnnularTiltedReference Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularKernelL2 Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.GaugeCoefficients.Physical.Allocation

private theorem assembleFirstRow_reverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (row : E →L[ℂ] F) (Q : F →L[ℂ] F) (h l k : E) (f slope : F)
    (equation : slope = Q (row (h + l + k) + f)) :
    Q (row (h + k)) + Q (f + row l) = slope := by
  rw [equation]
  simp only [map_add]
  abel

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)

/-- An arbitrary original candidate satisfying its full first physical row
has exactly the actual retained elimination, with all known sources once. -/
theorem strongCandidate_eliminated_of_fullFirst
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (first : highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength candidate.ofLp.1.ofLp.1 =
      highFullRestriction lower (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data candidate) +
        highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data))) :
    highBulkIntoFull lower (crossHighX lower length positive lengthPositive candidate.ofLp.1) =
      eliminatedXAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower length positive lengthPositive widthHalf widthLength
          (candidate.ofLp.1.ofLp.1,
            (strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2).weighted)) := by
  let corrected := strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2
  let input := fullHighEightPacket parameters lower length positive lengthPositive widthHalf widthLength
    (candidate.ofLp.1.ofLp.1,corrected.weighted)
  let h := highCrossSevenInput lower length positive lengthPositive candidate.ofLp.1
  let l := lowNormalizedSevenInput parameters lower length lengthPositive positive (candidate.ofLp.2.val 0)
  let k := knownLowSevenPacket lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let row := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
  let f := highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let slope := highBulkIntoFull lower
    (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength candidate.ofLp.1.ofLp.1)
  have sameSeven : assembledSevenBulk parameters lower positive (lowerHalf.trans (by norm_num)) 0
      (highBulkIntoFull lower (crossHighX lower length positive lengthPositive candidate.ofLp.1)) input = h + k :=
    (assembledSevenBulk_high parameters lower positive (lowerHalf.trans (by norm_num)) length lengthPositive widthHalf widthLength
      candidate.ofLp.1 corrected.weighted).trans
      (congrArg (fun packet : DivisionRow 7 lower => h + packet)
        (strongCorrectedHighData_sourcePacket parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2))
  have inputFirst : bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 8) input = slope :=
    fullHighEightPacket_first parameters lower length positive lengthPositive widthHalf widthLength candidate.ofLp.1.ofLp.1 corrected.weighted
  have inputLast : bulkMatrixUnit lower (0 : Fin 1) (7 : Fin 8) input = highRowProjection lower (f + row l) :=
    (fullHighEightPacket_f parameters lower length positive lengthPositive widthHalf widthLength candidate.ofLp.1.ofLp.1 corrected.weighted).trans
      (strongCorrectedHighData_f parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2)
  apply eliminatedX_of_assembledFirstRow parameters length compact lower positive (lowerHalf.trans (by norm_num)) state
  · exact fun mode low => highBulkIntoFull_low lower _ mode (not_le.mpr low)
  · rw [sameSeven,inputFirst,inputLast,highRowProjection_idempotent,highRowProjection_inclusion]
    exact assembleFirstRow_reverse row (highRowProjection lower) h l k f slope
      (congrArg (highBulkIntoFull lower) first)

end Grad.AnnularOriginalSmoothCore
