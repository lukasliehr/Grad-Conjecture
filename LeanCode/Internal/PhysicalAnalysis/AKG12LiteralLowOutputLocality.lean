import AKG11FullOriginalPacketAndRowLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKnownLow Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
  (included : lower ≤ upper)

/-- The literal positive radius in the full rV-rg row survives restriction. -/
theorem originalBulkRestriction_radius (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (radialRadiusRow lower lowerPositive field) =
      radialRadiusRow upper upperPositive (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae 1 lower upper included (radialRadiusRow lower lowerPositive field),
    (radialRadiusRow_ae lower lowerPositive field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    radialRadiusRow_ae upper upperPositive (originalBulkRestriction 1 lower upper included field),
    originalBulkRestriction_ae 1 lower upper included field] with radius restriction source target actual
  rw [restriction mode,source mode,target mode,actual mode]

theorem lowFirstOutput_restriction (parameters : PhaseParameters) (field : DivisionRow 1 lower) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included (lowFirstOutput parameters lower length field) =
      lowFirstOutput parameters upper length (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext index
  simp only [collarBulkRestriction_apply]
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included (lowFirstOutput parameters lower length field index),
    (lowFirstOutput_ae parameters lower length field index).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    lowFirstOutput_ae parameters upper length (originalBulkRestriction 1 lower upper included field) index,
    originalBulkRestriction_ae 1 lower upper included field] with radius restriction source target actual
  rw [restriction,source,target,actual index.2.val]

theorem lowCellOutput_restriction (field : DivisionRow 1 lower) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included (lowCellOutput lower length lowerPositive field) =
      lowCellOutput upper length upperPositive (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext index
  simp only [collarBulkRestriction_apply]
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included (lowCellOutput lower length lowerPositive field index),
    (lowCellOutput_ae lower length lowerPositive field index).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    lowCellOutput_ae upper length upperPositive (originalBulkRestriction 1 lower upper included field) index,
    originalBulkRestriction_ae 1 lower upper included field] with radius restriction source target actual
  rw [restriction,source,target,actual index.2.val]

theorem lowAngularOutput_restriction (field : DivisionRow 1 lower) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included (lowAngularOutput lower length lowerPositive field) =
      lowAngularOutput upper length upperPositive (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext index
  simp only [collarBulkRestriction_apply]
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included (lowAngularOutput lower length lowerPositive field index),
    (lowAngularOutput_ae lower length lowerPositive field index).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    lowAngularOutput_ae upper length upperPositive (originalBulkRestriction 1 lower upper included field) index,
    originalBulkRestriction_ae 1 lower upper included field] with radius restriction source target actual
  rw [restriction,source,target,actual index.2.val]

theorem lowCommonDiagonal_restriction (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (field : LowEnergyBulk lower) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included
      (lowCommonDiagonal parameters length lower lengthPositive lowerPositive field) =
    lowCommonDiagonal parameters length upper lengthPositive upperPositive
      (collarBulkRestriction LowAnnularIndex 1 lower upper included field) := by
  apply lp.ext
  funext index
  simp only [collarBulkRestriction_apply]
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included
      (lowCommonDiagonal parameters length lower lengthPositive lowerPositive field index),
    (lowCommonDiagonal_ae parameters length lower lengthPositive lowerPositive field index).filter_mono
      (ae_mono (collarMeasure_le lower upper included)),
    lowCommonDiagonal_ae parameters length upper lengthPositive upperPositive
      (collarBulkRestriction LowAnnularIndex 1 lower upper included field) index,
    collarL2Restriction_ae 1 lower upper included (field index)] with radius restriction source target actual
  rw [restriction,source,target]
  change _ = _ • (collarL2Restriction 1 lower upper included (field index) radius)
  rw [actual]

end Grad.AnnularRestriction
