import AKN24UniformPrimitiveSourceBounds
import AIY6ExactStrengthenedAngularSource

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.SourceCollarBulk Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.AnnularStrongData
open Grad.GaugeCoefficients.Physical.Allocation Grad.SourceCollarCoefficients Grad.AnnularHighTilt Grad.AnnularCurrentEnergy Grad.AnnularVariational

theorem divisionHighWeight_sourceAngular (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (sourceAngularBulk lower field) =
      sourceAngularBulk lower (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode]
  change _ = sourceAngularRatio mode • divisionHighWeight lower positive bounded field mode
  rw [divisionHighWeight_mode]
  exact (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)).map_smul _ _

theorem divisionHighWeight_bulkInclusion (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded
      (annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega) field) =
    annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
      (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode]
  change _ = sourceGradeRatio 0 0 1 0 mode • divisionHighWeight lower positive bounded field mode
  rw [divisionHighWeight_mode]
  exact ((scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)).restrictScalars ℝ).map_smul _ _

theorem actualOriginalF0Bulk_tilted_bound (parameters : PhaseParameters)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ ≤
      tiltedForceConstant (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ := by
  rw [unweightedSourceF0Bulk, ContinuousLinearMap.comp_apply, divisionHighWeight_bulkInclusion]
  have bound := lpTwoMap_bound (sourceGradeFamily (RadialL2 1 lower) 0 0 1 0) 1 zero_le_one
    (sourceGradeFamily_bound (RadialL2 1 lower) 0 0 1 0 (by omega) (by omega))
    (divisionHighWeight lower positive bounded.le (annularSourceCoordinate parameters 1 lower 1 0 0
      (actualOriginalF0Graph parameters lower positive bounded grade source)))
  have boundedRow : ‖annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
      (divisionHighWeight lower positive bounded.le (annularSourceCoordinate parameters 1 lower 1 0 0
        (actualOriginalF0Graph parameters lower positive bounded grade source)))‖ ≤
      ‖divisionHighWeight lower positive bounded.le (annularSourceCoordinate parameters 1 lower 1 0 0
        (actualOriginalF0Graph parameters lower positive bounded grade source))‖ := by
    simpa only [annularBulkInclusion, one_mul] using bound
  exact boundedRow.trans
    (actualOriginalF0Graph_tilted_coordinate_bound parameters source flat lower positive bounded grade)

theorem actualOriginalRF0Bulk_tilted_bound (parameters : PhaseParameters)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceRF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ ≤
      tiltedForceConstant (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ := by
  rw [unweightedSourceRF0Bulk, ContinuousLinearMap.comp_apply]
  change ‖divisionHighWeight lower positive bounded.le (sourceAngularBulk lower _)‖ ≤ _
  rw [divisionHighWeight_sourceAngular]
  exact (sourceAngularBulk_bound lower _).trans
    (actualOriginalF0Graph_tilted_coordinate_bound parameters source flat lower positive bounded grade)

/-- The strengthened original G3 coordinate is made from the actual SCS
value and its actual RG3. Every original full correction is retained. -/
def actualOriginalG3Row (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) : DivisionRow 1 lower :=
  strengthenedG lower
    (g3ValueRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
      (quotientEta parameters (grade + 6) source))
    (g3AngularRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
      (quotientEta parameters (grade + 6) source))

theorem actualOriginalG3Row_decode (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    originalAngularDecode lower (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source) =
      g3ValueRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
        (quotientEta parameters (grade + 6) source) ∧
    sourceAngularBulk lower (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source) =
      g3AngularRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
        (quotientEta parameters (grade + 6) source) := by
  apply strengthenedG_decode
  intro mode
  exact g3AngularRow_mode parameters L rho epsilon field small lower positive bounded (by omega) _ mode

theorem actualOriginalG3Row_tilted_pair_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ) :
    let estimate := tiltedG3HighConstant parameters L (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ +
      3 * tiltedCoefficientLowConstant parameters L (grade + 1) * physicalBudget parameters field rho epsilon (grade + 6) *
        ‖quotientEta parameters 5 source‖
    ‖divisionHighWeight lower positive bounded (originalAngularDecode lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source))‖ ≤ estimate ∧
    ‖divisionHighWeight lower positive bounded (sourceAngularBulk lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source))‖ ≤ estimate := by
  rw [(actualOriginalG3Row_decode parameters L rho epsilon field small lower positive bounded grade source).1,
    (actualOriginalG3Row_decode parameters L rho epsilon field small lower positive bounded grade source).2]
  exact actualG3_pair_tilted_bound parameters L rho epsilon field small source flat le_rfl lower positive bounded

end Grad.ExhaustionSourceAllocation
