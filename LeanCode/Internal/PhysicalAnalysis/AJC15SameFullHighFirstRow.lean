import AJC14LiteralEightInputProjections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution Grad.AnnularCircularForm
open Grad.AnnularCurrentGreen Grad.AnnularTiltedReference Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularReconstruction Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCoupledInverse
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.GaugeCoefficients.Physical.Allocation

theorem highRowProjection_inclusion (lower : ℝ) (field : AnnularBulk lower) :
    highRowProjection lower (highBulkIntoFull lower field) = highBulkIntoFull lower field :=
  (highRowProjection_fixed_iff lower _).mpr (highBulkIntoFull_low lower field)

theorem highRowProjection_idempotent (lower : ℝ) (field : DivisionRow 1 lower) :
    highRowProjection lower (highRowProjection lower field) = highRowProjection lower field :=
  highRowProjection_inclusion lower (highFullRestriction lower field)

private theorem assembleFirstRow {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (row : E →L[ℂ] F) (Q : F →L[ℂ] F) (h l k : E) (f slope : F)
    (equation : Q (row (h + k)) + Q (f + row l) = slope) :
    slope = Q (row (h + l + k) + f) := by
  rw [← equation]
  simp only [map_add]
  abel

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)

/-- The actual high physical derivative equals the high projection of the
full original first row, with the full prescribed f and each source once. -/
theorem sharedStrongResponse_fullHighFirstRow
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    highBulkIntoFull lower (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength solution.ofLp.1.ofLp.1) =
      highRowProjection lower
        (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
          (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) +
        highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)) := by
  let solution : CoupledSpace lower L positive lengthPositive :=
    sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let corrected : ActualHighGraphKnownData parameters lower 0 0 :=
    strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2
  let input : DivisionRow 8 lower := fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength
    (solution.ofLp.1.ofLp.1, corrected.weighted)
  let h : DivisionRow 7 lower := highCrossSevenInput lower L positive lengthPositive solution.ofLp.1
  let l : DivisionRow 7 lower := lowNormalizedSevenInput parameters lower L lengthPositive positive (solution.ofLp.2.val 0)
  let k : DivisionRow 7 lower := knownLowSevenPacket lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let row : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower := lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
  let f : DivisionRow 1 lower := highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let slope : DivisionRow 1 lower := highBulkIntoFull lower
    (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength solution.ofLp.1.ofLp.1)
  have sameSeven : eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input = h + k :=
    (coupledEliminatedSeven_same parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)).trans
      (congrArg (fun packet : DivisionRow 7 lower => h + packet)
        (strongCorrectedHighData_sourcePacket parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2))
  have first : bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 8) input = slope :=
    fullHighEightPacket_first parameters lower L positive lengthPositive widthHalf widthLength solution.ofLp.1.ofLp.1 corrected.weighted
  have last : bulkMatrixUnit lower (0 : Fin 1) (7 : Fin 8) input = highRowProjection lower (f + row l) :=
    (fullHighEightPacket_f parameters lower L positive lengthPositive widthHalf widthLength solution.ofLp.1.ofLp.1 corrected.weighted).trans
      (strongCorrectedHighData_f parameters L compact lower positive lowerHalf lengthPositive state data solution.ofLp.2)
  have equation := completedEliminatedSeven_firstRow parameters L compact lower positive (lowerHalf.trans (by norm_num)) state input
  rw [sameSeven, first, last, highRowProjection_idempotent, highRowProjection_inclusion] at equation
  exact assembleFirstRow row (highRowProjection lower) h l k f slope equation

end Grad.AnnularStrongSolution
