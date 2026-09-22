import AJC10CompletedHighPacketAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularCurrentSolution
open Grad.AnnularPhysicalSolution Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCrossMaps Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularFullSource Grad.GaugeCoefficients.Physical.Allocation

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

/-- The high projection of the actual full physical x,c,rV packet. Its
seven-slot input contains the prescribed three source entries exactly once. -/
def fullStrongHighPacket
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : DivisionRow 3 lower :=
  let seven := fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution
  let g := (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2
  bulkMatrixUnit lower (0 : Fin 3) 0 (highBulkIntoFull lower (crossHighX lower L positive lengthPositive solution.ofLp.1)) +
    bulkMatrixUnit lower (1 : Fin 3) 0 (highRowProjection lower
      (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1 seven)) +
    bulkMatrixUnit lower (2 : Fin 3) 0 (highRowProjection lower
      (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2 seven - radialRadiusRow lower positive g))

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)

/-- The same coupled inverse's actual high physical output is the high
projection of the full shared-source reconstruction, without duplicating sources. -/
theorem sharedStrongPhysicalOutput_sameFull
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data) =
    fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  let solution : CoupledSpace lower L positive lengthPositive :=
    sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
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
    coupledEliminatedX_same parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)
  have sameSeven : eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input = h + k :=
    (coupledEliminatedSeven_same parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)).trans
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

end Grad.AnnularStrongSolution
