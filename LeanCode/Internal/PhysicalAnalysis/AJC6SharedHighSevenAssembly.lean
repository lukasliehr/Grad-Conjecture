import AJC5ExactKnownSevenSelection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution
open Grad.AnnularCrossMaps Grad.AnnularKnownLow Grad.AnnularTiltedReference
open Grad.AnnularReconstruction Grad.AnnularFullSource

private theorem selectFourAndKnown {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (selector : E →L[ℂ] F) (first angular cell radius known : E)
    (selectedAngular selectedCell selectedRadius selectedKnown : F)
    (firstZero : selector first = 0) (angularEq : selector angular = selectedAngular)
    (cellEq : selector cell = selectedCell) (radiusEq : selector radius = selectedRadius)
    (knownEq : selector known = selectedKnown) :
    selector ((first + angular + cell + radius) + known) =
      selectedAngular + selectedCell + selectedRadius + selectedKnown := by
  rw [map_add, map_add, map_add, map_add, firstZero, angularEq, cellEq, radiusEq, knownEq, zero_add]

private theorem addKnownSlots {E : Type*} [AddCommGroup E] (x a b c d : E) :
    x + (a + b + c + d) = x + a + b + c + d := by abel

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)

theorem knownSevenBulkAction_source (source : HighKnownSourceBulk lower) :
    knownSevenBulkAction parameters lower positive bounded 0 (highKnownEightPacket lower source) =
      knownLowSevenPacket lower source := by
  have slot4 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (4 : Fin 8) 0 (source 0)) = bulkMatrixUnit lower (4 : Fin 7) 0 (source 0) :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (4 : Fin 7) (source 0)).trans (if_neg (by decide))
  have slot5 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (5 : Fin 8) 0 (source 1)) = bulkMatrixUnit lower (5 : Fin 7) 0 (source 1) :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (5 : Fin 7) (source 1)).trans (if_neg (by decide))
  have slot6 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (6 : Fin 8) 0 (source 2)) = bulkMatrixUnit lower (6 : Fin 7) 0 (source 2) :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (6 : Fin 7) (source 2)).trans (if_neg (by decide))
  change knownSevenBulkAction parameters lower positive bounded 0
    (bulkMatrixUnit lower (4 : Fin 8) 0 (source 0) + bulkMatrixUnit lower (5 : Fin 8) 0 (source 1) +
      bulkMatrixUnit lower (6 : Fin 8) 0 (source 2) + bulkMatrixUnit lower (7 : Fin 8) 0 (source 3)) = _
  rw [map_add, map_add, map_add, slot4, slot5, slot6, knownSevenBulkAction_last, add_zero]
  rfl

/-- The shared seven-slot source is unaffected by the high projection of f
or the low-to-high correction in f. Neither occupies a physical source slot. -/
theorem knownLowSevenPacket_same_sources (first second : HighKnownSourceBulk lower)
    (same0 : first 0 = second 0) (same1 : first 1 = second 1) (same2 : first 2 = second 2) :
    knownLowSevenPacket lower first = knownLowSevenPacket lower second := by
  change bulkMatrixUnit lower (4 : Fin 7) 0 (first 0) + bulkMatrixUnit lower (5 : Fin 7) 0 (first 1) +
    bulkMatrixUnit lower (6 : Fin 7) 0 (first 2) = _
  rw [same0, same1, same2]
  rfl

theorem assembledSevenBulk_high (L : ℝ) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : CrossHighSpace lower L positive lengthPositive) (source : HighKnownSourceBulk lower) :
    assembledSevenBulk parameters lower positive bounded 0
      (highBulkIntoFull lower (crossHighX lower L positive lengthPositive field))
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field.ofLp.1, source)) =
    highCrossSevenInput lower L positive lengthPositive field + knownLowSevenPacket lower source := by
  let decoded := bEnergyDecode lower L positive field.ofLp.1
  let first := highBulkIntoFull lower
    (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field.ofLp.1)
  let angular := highBulkIntoFull lower (highEnergyAngularRadius lower L positive decoded)
  let cell := highBulkIntoFull lower ((L : ℂ) • highEnergyCell lower L positive decoded)
  let radius := highBulkIntoFull lower (highEnergyRadius lower L positive decoded)
  have slot0 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (0 : Fin 8) 0 first) = 0 :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (0 : Fin 7) first).trans (if_pos rfl)
  have slot1 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (1 : Fin 8) 0 angular) = bulkMatrixUnit lower (1 : Fin 7) 0 angular :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (1 : Fin 7) angular).trans (if_neg (by decide))
  have slot2 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (2 : Fin 8) 0 cell) = bulkMatrixUnit lower (2 : Fin 7) 0 cell :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (2 : Fin 7) cell).trans (if_neg (by decide))
  have slot3 : knownSevenBulkAction parameters lower positive bounded 0
      (bulkMatrixUnit lower (3 : Fin 8) 0 radius) = bulkMatrixUnit lower (3 : Fin 7) 0 radius :=
    (knownSevenBulkAction_slot parameters lower positive bounded 0 (3 : Fin 7) radius).trans (if_neg (by decide))
  have selected := selectFourAndKnown (knownSevenBulkAction parameters lower positive bounded 0)
    _ _ _ _ _ _ _ _ _ slot0 slot1 slot2 slot3 (knownSevenBulkAction_source parameters lower positive bounded source)
  exact (congrArg (fun selected : DivisionRow 7 lower =>
    bulkMatrixUnit lower (0 : Fin 7) 0 (highBulkIntoFull lower (crossHighX lower L positive lengthPositive field)) + selected)
    selected).trans (addKnownSlots _ _ _ _ _)

end Grad.AnnularStrongSolution
