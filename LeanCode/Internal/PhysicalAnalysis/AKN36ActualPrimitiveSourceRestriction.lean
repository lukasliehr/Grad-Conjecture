import AKN35OriginalPrimitiveRestriction

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

theorem originalBulkRestriction_s11 {dimension : ℕ} (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (annularS11RowValue lower field) =
      annularS11RowValue upper (originalBulkRestriction dimension lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included (annularS11Ratio mode • field mode) =
    annularS11Ratio mode • collarL2Restriction dimension lower upper included (field mode)
  exact map_smul _ _ _

theorem originalBulkRestriction_lowering {dimension : ℕ} (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (annularWeightLoweringRowValue lower field) =
      annularWeightLoweringRowValue upper (originalBulkRestriction dimension lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included (annularWeightLoweringRatio mode • field mode) =
    annularWeightLoweringRatio mode • collarL2Restriction dimension lower upper included (field mode)
  exact map_smul _ _ _

theorem actualOriginalF0Graph_restrict (parameters : PhaseParameters) (lower upper : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower < 1) (boundedUpper : upper < 1) (grade : ℕ) (source : SmoothQuotient parameters) :
    sourceGraphRestriction parameters 1 lower upper included 1 0 0
      (actualOriginalF0Graph parameters lower positiveLower boundedLower grade source) =
    actualOriginalF0Graph parameters upper positiveUpper boundedUpper grade source := by
  apply annularSource_bulk_injective parameters 1 upper positiveUpper boundedUpper.le 1 0
  rw [sourceGraphRestriction_coordinate, actualOriginalF0Graph_value, actualOriginalF0Graph_value,
    originalBulkRestriction_s11, originalBulkRestriction_tangentialFrame, restrictedCore_row_restrict]

theorem actualOriginalF2Graph_restrict (parameters : PhaseParameters) (L lower upper : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower < 1) (boundedUpper : upper < 1) (grade : ℕ) (source : SmoothQuotient parameters) :
    sourceGraphRestriction parameters 1 lower upper included 0 0 0
      (actualOriginalF2Graph parameters L lower positiveLower boundedLower grade source) =
    actualOriginalF2Graph parameters L upper positiveUpper boundedUpper grade source := by
  apply annularSource_bulk_injective parameters 1 upper positiveUpper boundedUpper.le 0 0
  rw [sourceGraphRestriction_coordinate, actualOriginalF2Graph_value, actualOriginalF2Graph_value,
    map_smul, restrictedCore_row_restrict]

theorem actualOriginalF1Row_restrict (parameters : PhaseParameters) (lower upper : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower ≤ 1) (boundedUpper : upper ≤ 1) (grade : ℕ) (source : SmoothQuotient parameters) :
    originalBulkRestriction 1 lower upper included
      (actualOriginalF1Row parameters lower positiveLower boundedLower grade source) =
    actualOriginalF1Row parameters upper positiveUpper boundedUpper grade source := by
  rw [actualOriginalF1Row_value, actualOriginalF1Row_value,
    originalBulkRestriction_lowering, originalBulkRestriction_radialFrame, restrictedCore_row_restrict]

end Grad.ExhaustionSourceAllocation
