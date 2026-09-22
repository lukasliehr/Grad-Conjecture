import AJZ4FullOriginalBulkRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.AnnularStrongData Grad.AnnularCurrentSource Grad.AnnularHighTilt

theorem originalBulkRestriction_splitInclusion (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper)
    (lowAngular lowCell highAngular highCell : ℕ)
    (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceBulk parameters dimension lower highAngular highCell) :
    originalBulkRestriction dimension lower upper included
        (annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) =
      annularBulkInclusion parameters dimension upper lowAngular lowCell highAngular highCell angularLe cellLe
        (originalBulkRestriction dimension lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included
      (sourceGradeRatio lowAngular lowCell highAngular highCell mode • field mode) =
    sourceGradeRatio lowAngular lowCell highAngular highCell mode •
      collarL2Restriction dimension lower upper included (field mode)
  exact (collarL2Restriction dimension lower upper included).map_smul_of_tower _ _

theorem originalBulkRestriction_F0 (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : HighF0SourceGraph parameters lower) :
    originalBulkRestriction 1 lower upper included (unweightedSourceF0Bulk parameters lower field) =
      unweightedSourceF0Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 1 0 0 field) := by
  change originalBulkRestriction 1 lower upper included
    (annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
      (annularSourceCoordinate parameters 1 lower 1 0 0 field)) = _
  rw [originalBulkRestriction_splitInclusion, ← sourceGraphRestriction_coordinate parameters 1 lower upper included 1 0 0]
  rfl

theorem originalBulkRestriction_RF0 (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : HighF0SourceGraph parameters lower) :
    originalBulkRestriction 1 lower upper included (unweightedSourceRF0Bulk parameters lower field) =
      unweightedSourceRF0Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 1 0 0 field) := by
  change originalBulkRestriction 1 lower upper included
    (sourceAngularBulk lower (annularSourceCoordinate parameters 1 lower 1 0 0 field)) = _
  rw [originalBulkRestriction_angularBulk, ← sourceGraphRestriction_coordinate parameters 1 lower upper included 1 0 0]
  rfl

theorem originalBulkRestriction_F2 (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : HighF2SourceGraph parameters lower) :
    originalBulkRestriction 1 lower upper included (unweightedSourceF2Bulk parameters lower field) =
      unweightedSourceF2Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 0 0 0 field) :=
  (sourceGraphRestriction_coordinate parameters 1 lower upper included 0 0 0 field 0).symm

theorem collarL2Restriction_scalarRadialMap (lower upper : ℝ) (included : lower ≤ upper)
    (first second : C(ℝ, ℝ)) (firstBound secondBound : ℝ)
    (firstLaw : ∀ r ∈ Icc lower 1, |first r| ≤ firstBound)
    (secondLaw : ∀ r ∈ Icc upper 1, |second r| ≤ secondBound)
    (same : EqOn first second (Icc upper 1)) (field : RadialL2 1 lower) :
    collarL2Restriction 1 lower upper included (scalarRadialMap lower first firstBound firstLaw field) =
      scalarRadialMap upper second secondBound secondLaw (collarL2Restriction 1 lower upper included field) := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included (scalarRadialMap lower first firstBound firstLaw field),
    (scalarRadialMap_ae lower first firstBound firstLaw field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    scalarRadialMap_ae upper second secondBound secondLaw (collarL2Restriction 1 lower upper included field),
    collarL2Restriction_ae 1 lower upper included field,
    ae_restrict_mem measurableSet_Icc] with radius restriction source target actual inside
  rw [restriction, source, target, actual, same inside]

theorem originalBulkRestriction_highWeight (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper ≤ 1)
    (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (divisionHighWeight lower positiveLower (included.trans bounded) field) =
      divisionHighWeight upper positiveUpper bounded (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  exact collarL2Restriction_scalarRadialMap lower upper included
    (highPowerCurve lower (-highTiltExponent) positiveLower)
    (highPowerCurve upper (-highTiltExponent) positiveUpper)
    (lower ^ (-highTiltExponent)) (upper ^ (-highTiltExponent))
    (highNegativePower_bound lower positiveLower (included.trans bounded))
    (highNegativePower_bound upper positiveUpper bounded)
    (fun radius inside => by
      rw [highPowerCurve_physical lower (-highTiltExponent) positiveLower radius ⟨included.trans inside.1, inside.2⟩,
        highPowerCurve_physical upper (-highTiltExponent) positiveUpper radius inside]) (field mode)

theorem originalBulkRestriction_highUnweight (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper ≤ 1)
    (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (divisionHighUnweight lower positiveLower (included.trans bounded) field) =
      divisionHighUnweight upper positiveUpper bounded (originalBulkRestriction 1 lower upper included field) := by
  apply lp.ext
  funext mode
  exact collarL2Restriction_scalarRadialMap lower upper included
    (highPowerCurve lower highTiltExponent positiveLower)
    (highPowerCurve upper highTiltExponent positiveUpper) 1 1
    (highPositivePower_bound lower positiveLower (included.trans bounded))
    (highPositivePower_bound upper positiveUpper bounded)
    (fun radius inside => by
      rw [highPowerCurve_physical lower highTiltExponent positiveLower radius ⟨included.trans inside.1, inside.2⟩,
        highPowerCurve_physical upper highTiltExponent positiveUpper radius inside]) (field mode)

end Grad.AnnularRestriction
