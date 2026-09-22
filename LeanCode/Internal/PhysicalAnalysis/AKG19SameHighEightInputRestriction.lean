import AKG18SameOriginalWeakRowsOnSmallerCollar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularTiltedReference
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem highEight_fourSum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (restriction : E →L[ℂ] F) (a b c d : E) :
    restriction (a + b + c + d) = restriction a + restriction b + restriction c + restriction d := by
  rw [map_add,map_add,map_add]

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (included : lower ≤ upper)

theorem highEnergyRestriction_radius (field : annularEnergySpace lower length lowerPositive) :
    highEnergyRadius upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    collarBulkRestriction HighAnnularMode 1 lower upper included (highEnergyRadius lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  rw [collarBulkRestriction_apply,highEnergyRadius_mode,highEnergyRadius_mode,
    collarL2Restriction_scalar 1 lower upper included _ _
      (highReciprocalRadius_restriction lower upper included lowerPositive upperPositive),highEnergyRestriction_value]
  rfl

theorem highEnergyRestriction_angularRadius (field : annularEnergySpace lower length lowerPositive) :
    highEnergyAngularRadius upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    collarBulkRestriction HighAnnularMode 1 lower upper included (highEnergyAngularRadius lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  rw [collarBulkRestriction_apply,highEnergyAngularRadius_mode,highEnergyAngularRadius_mode,map_smul]
  exact congrArg (fun value : RadialL2 1 upper => (Complex.I * (mode.val.1 : ℂ)) • value)
    (congrArg (fun value : AnnularBulk upper => value mode)
      (highEnergyRestriction_radius lower upper length lowerPositive upperPositive included field))

theorem highEnergyRestriction_physicalCell (field : annularEnergySpace lower length lowerPositive) :
    highEnergyCell upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    collarBulkRestriction HighAnnularMode 1 lower upper included (highEnergyCell lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  rw [collarBulkRestriction_apply,highEnergyCell_mode,highEnergyCell_mode,map_smul,highEnergyRestriction_value]
  rfl

theorem highBulkSlot_restriction {dimension : ℕ} (slot : Fin dimension) (field : AnnularBulk lower) :
    originalBulkRestriction dimension lower upper included (highBulkSlot lower slot field) =
      highBulkSlot upper slot (collarBulkRestriction HighAnnularMode 1 lower upper included field) := by
  change originalBulkRestriction dimension lower upper included (bulkMatrixUnit lower slot 0 (highBulkIntoFull lower field)) = _
  rw [bulkMatrixUnit_restriction,highBulkIntoFull_restriction]
  rfl

variable (parameters : PhaseParameters) (upperBounded : upper < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

include upperBounded in
theorem highEightEnergyPacket_restriction (field : annularEnergySpace lower length lowerPositive) :
    originalBulkRestriction 8 lower upper included
      (highEightEnergyPacket parameters lower length lowerPositive lengthPositive widthHalf widthLength field) =
    highEightEnergyPacket parameters upper length upperPositive lengthPositive widthHalf widthLength
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) := by
  let decoded := bEnergyDecode lower length lowerPositive field
  have decode := highEnergyRestriction_bDecode lower upper length lowerPositive upperPositive upperBounded included field
  have phase := (highEnergyRestriction_physicalDerivative parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included widthHalf widthLength field).symm
  have angular := (highEnergyRestriction_angularRadius lower upper length lowerPositive upperPositive included decoded).symm.trans
    (congrArg (highEnergyAngularRadius upper length upperPositive) decode)
  have cell := (highEnergyRestriction_physicalCell lower upper length lowerPositive upperPositive included decoded).symm.trans
    (congrArg (highEnergyCell upper length upperPositive) decode)
  have radius := (highEnergyRestriction_radius lower upper length lowerPositive upperPositive included decoded).symm.trans
    (congrArg (highEnergyRadius upper length upperPositive) decode)
  have first := (highBulkSlot_restriction lower upper included (0 : Fin 8) _).trans
    (congrArg (highBulkSlot upper (0 : Fin 8)) phase)
  have second := (highBulkSlot_restriction lower upper included (1 : Fin 8) _).trans
    (congrArg (highBulkSlot upper (1 : Fin 8)) angular)
  have third := (highBulkSlot_restriction lower upper included (2 : Fin 8) _).trans
    (congrArg (highBulkSlot upper (2 : Fin 8))
      ((map_smul (collarBulkRestriction HighAnnularMode 1 lower upper included) (length : ℂ) _).trans
        (congrArg (fun value : AnnularBulk upper => (length : ℂ) • value) cell)))
  have fourth := (highBulkSlot_restriction lower upper included (3 : Fin 8) _).trans
    (congrArg (highBulkSlot upper (3 : Fin 8)) radius)
  exact (highEight_fourSum (originalBulkRestriction 8 lower upper included) _ _ _ _).trans
    (congrArg₂ (fun a b : DivisionRow 8 upper => a + b)
      (congrArg₂ (fun a b : DivisionRow 8 upper => a + b)
        (congrArg₂ (fun a b : DivisionRow 8 upper => a + b) first second) third) fourth)

omit parameters upperBounded lengthPositive widthHalf widthLength lowerPositive upperPositive length in
 theorem highKnownEightPacket_restriction (known : HighKnownSourceBulk lower) :
    originalBulkRestriction 8 lower upper included (highKnownEightPacket lower known) =
      highKnownEightPacket upper (knownRowsRestriction lower upper included known) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae 8 lower upper included (highKnownEightPacket lower known),
    (highKnownEightPacket_ae lower known).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    highKnownEightPacket_ae upper (knownRowsRestriction lower upper included known),
    originalBulkRestriction_ae 1 lower upper included (known 0), originalBulkRestriction_ae 1 lower upper included (known 1),
    originalBulkRestriction_ae 1 lower upper included (known 2), originalBulkRestriction_ae 1 lower upper included (known 3)]
    with radius restriction source target first second third fourth
  rw [restriction mode,source mode,target mode]
  change _ = ((originalBulkRestriction 1 lower upper included (known 0) mode radius) 0) • _ +
    ((originalBulkRestriction 1 lower upper included (known 1) mode radius) 0) • _ +
    ((originalBulkRestriction 1 lower upper included (known 2) mode radius) 0) • _ +
    ((originalBulkRestriction 1 lower upper included (known 3) mode radius) 0) • _
  rw [first mode,second mode,third mode,fourth mode]

include upperBounded in
 theorem fullHighEightPacket_restriction (field : annularEnergySpace lower length lowerPositive) (known : HighKnownSourceBulk lower) :
    originalBulkRestriction 8 lower upper included
      (fullHighEightPacket parameters lower length lowerPositive lengthPositive widthHalf widthLength (field,known)) =
    fullHighEightPacket parameters upper length upperPositive lengthPositive widthHalf widthLength
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field,knownRowsRestriction lower upper included known) := by
  change originalBulkRestriction 8 lower upper included
    (highEightEnergyPacket parameters lower length lowerPositive lengthPositive widthHalf widthLength field + highKnownEightPacket lower known) = _
  rw [map_add,highEightEnergyPacket_restriction lower upper length lowerPositive upperPositive included parameters upperBounded lengthPositive widthHalf widthLength,
    highKnownEightPacket_restriction]
  rfl

end Grad.AnnularRestriction
