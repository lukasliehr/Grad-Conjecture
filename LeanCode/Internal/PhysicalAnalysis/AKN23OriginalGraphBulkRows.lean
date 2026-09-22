import AKN22ActualOriginalRadialSourceGraphs

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.SourceCollarBulk Grad.SourceCollarRestriction Grad.SourceCollarAngular Grad.SourceCollarFullSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection

theorem restrictionRow_core_grade_independent {dimension first second power radial : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (firstPaid : power + radial ≤ first) (secondPaid : power + radial ≤ second) :
    completedRestrictionRow (power := power) (radial := radial) lower positive bounded parameters firstPaid
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := first) field)) =
    completedRestrictionRow (power := power) (radial := radial) lower positive bounded parameters secondPaid
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := second) field)) := by
  rw [completedRestrictionRow_core, completedRestrictionRow_core]
  apply lp.ext
  funext mode
  rfl

theorem completedTangentialContraction_value (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (field : AGrade parameters 2 (power + 1)) :
    (completedTangentialContraction lower positive bounded parameters power 1 field).val 0 =
      tangentialRowContraction lower positive power
        (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) field) := rfl

theorem completedRadialContraction_value (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (field : AGrade parameters 2 (power + 1)) :
    (completedRadialContraction lower positive bounded parameters power 1 field).val 0 =
      radialRowContraction lower positive power
        (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) field) := rfl

/-- The actual force bulk at grade t is the normalized value of the same
SRC radial graph stored at grade t+1. -/
def actualOriginalF1Row (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) : DivisionRow 1 lower :=
  annularWeightLoweringRowValue lower
    ((completedForceRadial lower positive bounded parameters grade
      (quotientEta parameters (grade + 2) source)).val 0)

theorem actualOriginalF0Graph_value (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    annularSourceCoordinate parameters 1 lower 1 0 0
      (actualOriginalF0Graph parameters lower positive bounded grade source) =
      annularS11RowValue lower
        (tangentialRowContraction lower positive (grade + 1)
          (completedRestrictionRow (power := grade + 1) (radial := 0) lower positive bounded.le parameters (by omega)
            (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 2) (cartesianSourceVector source))))) := by
  rw [actualOriginalF0Graph_coordinate]
  change annularS11RowValue lower ((completedForceTangential lower positive bounded.le parameters grade
    (quotientEta parameters (grade + 2) source)).val 0) = _
  rw [completedForceTangential_core]
  rfl

theorem actualOriginalF2Graph_value (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    annularSourceCoordinate parameters 1 lower 0 0 0
      (actualOriginalF2Graph parameters L lower positive bounded grade source) =
      (L : ℂ)⁻¹ • completedRestrictionRow (power := grade) (radial := 0)
        lower positive bounded.le parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 1) (source 3))) := by
  rw [actualOriginalF2Graph_coordinate, completedFourthSource_core]
  rfl

theorem actualOriginalF1Row_value (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    actualOriginalF1Row parameters lower positive bounded grade source =
      annularWeightLoweringRowValue lower
        (radialRowContraction lower positive (grade + 1)
          (completedRestrictionRow (power := grade + 1) (radial := 0) lower positive bounded parameters (by omega)
            (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 2) (cartesianSourceVector source))))) := by
  unfold actualOriginalF1Row
  rw [completedForceRadial_core]
  rfl

end Grad.ExhaustionSourceAllocation
