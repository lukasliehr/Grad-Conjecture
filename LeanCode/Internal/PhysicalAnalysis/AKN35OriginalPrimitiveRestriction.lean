import AKN32SameFullG3Grades
import AJZ6OriginalFullSourceBlockContraction

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularRestriction Grad.SourceCollarAngular

theorem originalBulkRestriction_shift {dimension : ℕ} (lower upper : ℝ) (included : lower ≤ upper)
    (power : ℕ) (shift : ℤ) (field : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (annularRowShift lower power shift field) =
      annularRowShift upper power shift (originalBulkRestriction dimension lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included
    (annularShiftScalar power shift mode • field (mode.1 - shift, mode.2)) =
      annularShiftScalar power shift mode • collarL2Restriction dimension lower upper included (field (mode.1 - shift, mode.2))
  exact map_smul _ _ _

theorem originalBulkRestriction_valueMap {sourceDimension targetDimension : ℕ}
    (lower upper : ℝ) (included : lower ≤ upper)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) :
    originalBulkRestriction targetDimension lower upper included (divisionRowValueMap lower mapping field) =
      divisionRowValueMap upper mapping (originalBulkRestriction sourceDimension lower upper included field) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae targetDimension lower upper included (divisionRowValueMap lower mapping field mode),
    (mapping.coeFn_compLpL (field mode)).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    mapping.coeFn_compLpL (collarL2Restriction sourceDimension lower upper included (field mode)),
    collarL2Restriction_ae sourceDimension lower upper included (field mode)] with radius restriction source target same
  change collarL2Restriction targetDimension lower upper included
      (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (field mode)) radius =
    (mapping.compLpL 2 (volume.restrict (Icc upper 1))
      (collarL2Restriction sourceDimension lower upper included (field mode))) radius
  change (collarL2Restriction targetDimension lower upper included
      (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (field mode))) radius =
    (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (field mode)) radius at restriction
  exact restriction.trans (source.trans (target.trans (congrArg mapping same)).symm)

theorem originalBulkRestriction_radialFrame (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (power : ℕ) (field : DivisionRow 2 lower) :
    originalBulkRestriction 1 lower upper included (radialRowContraction lower positiveLower power field) =
      radialRowContraction upper positiveUpper power (originalBulkRestriction 2 lower upper included field) := by
  rw [radialRowContraction_formula, radialRowContraction_formula, map_add,
    originalBulkRestriction_valueMap, originalBulkRestriction_valueMap]
  unfold cosineRow sineRow
  simp only [map_smul, map_add, map_sub, originalBulkRestriction_shift]

theorem originalBulkRestriction_tangentialFrame (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (power : ℕ) (field : DivisionRow 2 lower) :
    originalBulkRestriction 1 lower upper included (tangentialRowContraction lower positiveLower power field) =
      tangentialRowContraction upper positiveUpper power (originalBulkRestriction 2 lower upper included field) := by
  rw [tangentialRowContraction_formula, tangentialRowContraction_formula, map_sub,
    originalBulkRestriction_valueMap, originalBulkRestriction_valueMap]
  unfold cosineRow sineRow
  simp only [map_smul, map_add, map_sub, originalBulkRestriction_shift]

theorem restrictionModeLp_restrict {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower upper : ℝ) (included : lower ≤ upper) (power radial : ℕ) (mode : ℤ × ℤ) :
    collarL2Restriction dimension lower upper included (restrictionModeLp lower power radial parameters field mode) =
      restrictionModeLp upper power radial parameters field mode := by
  unfold restrictionModeLp
  rw [map_smul]
  congr 1
  exact collarL2Restriction_weightedCurveLinear dimension lower upper included
    ⟨radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 radial,
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous⟩

theorem restrictedCore_row_restrict {dimension grade power radial : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower ≤ 1) (boundedUpper : upper ≤ 1) (paid : power + radial ≤ grade) :
    originalBulkRestriction dimension lower upper included
      (completedRestrictionRow (power := power) (radial := radial) lower positiveLower boundedLower parameters paid
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) =
    completedRestrictionRow (power := power) (radial := radial) upper positiveUpper boundedUpper parameters paid
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) := by
  rw [completedRestrictionRow_core, completedRestrictionRow_core]
  apply lp.ext
  funext mode
  exact restrictionModeLp_restrict parameters field lower upper included power radial mode

end Grad.ExhaustionSourceAllocation
