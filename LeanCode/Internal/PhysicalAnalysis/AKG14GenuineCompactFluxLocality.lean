import AKG13HighPhysicalDerivativeLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularTiltedReference
open Grad.AnnularReconstruction Grad.AnnularPhysicalSolution
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower upper : ℝ) (included : lower ≤ upper)
include included

theorem bulkMatrixUnit_restriction {input output : ℕ} (row : Fin output) (column : Fin input)
    (field : DivisionRow input lower) :
    originalBulkRestriction output lower upper included (bulkMatrixUnit lower row column field) =
      bulkMatrixUnit upper row column (originalBulkRestriction input lower upper included field) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae output lower upper included (bulkMatrixUnit lower row column field),
    (bulkMatrixUnit_ae lower row column field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    bulkMatrixUnit_ae upper row column (originalBulkRestriction input lower upper included field),
    originalBulkRestriction_ae input lower upper included field] with radius restriction source target actual
  rw [restriction mode,source mode,target mode,actual mode]

theorem highPhysicalOutput_restriction {dimension : ℕ} (slot : Fin dimension)
    (field : DivisionRow dimension lower) (mode : HighAnnularMode) :
    collarL2Restriction 1 lower upper included (highPhysicalOutput lower slot field mode) =
      highPhysicalOutput upper slot (originalBulkRestriction dimension lower upper included field) mode :=
  congrArg (fun result : DivisionRow 1 upper => result mode.val)
    (bulkMatrixUnit_restriction lower upper included (0 : Fin 1) slot field)

variable (lowerPositive : 0 < lower) (upperPositive : 0 < upper)

theorem annularRadialMoment_restriction (field : RadialL2 1 lower) :
    collarL2Restriction 1 lower upper included (annularRadialMoment lower lowerPositive field) =
      annularRadialMoment upper upperPositive (collarL2Restriction 1 lower upper included field) := by
  change collarL2Restriction 1 lower upper included (collarScalar 1 lower annularRadiusCurve
    (radialOrdinary 1 lower lowerPositive field)) = _
  rw [collarL2Restriction_scalar 1 lower upper included _ _ (fun _ _ => rfl),
    collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included]
  rfl

theorem annularInverseRadiusCurve_restriction :
    EqOn (annularInverseRadiusCurve lower lowerPositive) (annularInverseRadiusCurve upper upperPositive) (Icc upper 1) := by
  intro radius inside
  change 1 / max lower radius = 1 / max upper radius
  rw [max_eq_right (included.trans inside.1),max_eq_right inside.1]

theorem annularInverseRadiusSlope_restriction :
    EqOn (annularInverseRadiusSlope lower lowerPositive) (annularInverseRadiusSlope upper upperPositive) (Icc upper 1) := by
  intro radius inside
  change -(annularInverseRadiusCurve lower lowerPositive radius * annularInverseRadiusCurve lower lowerPositive radius) =
    -(annularInverseRadiusCurve upper upperPositive radius * annularInverseRadiusCurve upper upperPositive radius)
  rw [annularInverseRadiusCurve_restriction lower upper included lowerPositive upperPositive inside]

theorem highReciprocalRadius_restriction :
    EqOn (highReciprocalRadius lower lowerPositive) (highReciprocalRadius upper upperPositive) (Icc upper 1) := by
  intro radius inside
  change (max lower radius)⁻¹ = (max upper radius)⁻¹
  rw [max_eq_right (included.trans inside.1),max_eq_right inside.1]

variable (parameters : PhaseParameters) (length : ℝ)

theorem annularTiltCurve_restriction (cell : ℤ) :
    EqOn (annularTiltCurve parameters lower lowerPositive cell) (annularTiltCurve parameters upper upperPositive cell) (Icc upper 1) := by
  intro radius inside
  change annularPhaseSlope parameters cell radius - annularTiltExponent / max lower radius =
    annularPhaseSlope parameters cell radius - annularTiltExponent / max upper radius
  rw [max_eq_right (included.trans inside.1),max_eq_right inside.1]

theorem physicalFluxMomentRHS_restriction (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    collarL2Restriction 1 lower upper included (physicalFluxMomentRHS parameters lower length lowerPositive field mode) =
      physicalFluxMomentRHS parameters upper length upperPositive (originalBulkRestriction 3 lower upper included field) mode := by
  unfold physicalFluxMomentRHS
  rw [map_sub,map_sub,map_smul,map_smul,
    collarL2Restriction_scalar 1 lower upper included _ _
      (annularTiltCurve_restriction lower upper included lowerPositive upperPositive parameters mode.val.2),
    collarL2Restriction_scalar 1 lower upper included _ _
      (highReciprocalRadius_restriction lower upper included lowerPositive upperPositive)]
  rw [annularRadialMoment_restriction,annularRadialMoment_restriction,annularRadialMoment_restriction,
    highPhysicalOutput_restriction,highPhysicalOutput_restriction,highPhysicalOutput_restriction]

theorem physicalFluxOrdinarySlope_restriction (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    collarL2Restriction 1 lower upper included (physicalFluxOrdinarySlope parameters lower length lowerPositive field mode) =
      physicalFluxOrdinarySlope parameters upper length upperPositive (originalBulkRestriction 3 lower upper included field) mode := by
  unfold physicalFluxOrdinarySlope
  rw [map_add,
    collarL2Restriction_scalar 1 lower upper included _ _
      (annularInverseRadiusSlope_restriction lower upper included lowerPositive upperPositive),
    collarL2Restriction_scalar 1 lower upper included _ _
      (annularInverseRadiusCurve_restriction lower upper included lowerPositive upperPositive),
    annularRadialMoment_restriction,highPhysicalOutput_restriction,physicalFluxMomentRHS_restriction]

/-- Genuine weak-to-compact testing on the smaller collar, on the SAME
restricted completed physical output, with both original negative output derivatives. -/
theorem compactPhysicalPacketEquation_restriction (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower length lowerPositive lengthPositive widthHalf widthLength field) :
    CompactPhysicalPacketEquation parameters upper length upperPositive lengthPositive widthHalf widthLength
      (originalBulkRestriction 3 lower upper included field) := by
  apply compactPhysicalPacketEquation_of_ordinaryWeak parameters upper length upperPositive upperBounded lengthPositive widthHalf widthLength
  intro mode
  have source := (compactPhysicalPacketEquation_iff_ordinaryWeak parameters lower length lowerPositive
    (included.trans_lt upperBounded) lengthPositive widthHalf widthLength field).mp equation mode
  have actual := collarWeakDerivative_restrict 1 lower upper included upperPositive upperBounded _ _ source
  rw [collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included,
    highPhysicalOutput_restriction,physicalFluxOrdinarySlope_restriction] at actual
  exact actual

end Grad.AnnularRestriction
