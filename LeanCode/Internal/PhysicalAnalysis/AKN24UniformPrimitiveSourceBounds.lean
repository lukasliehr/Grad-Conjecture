import AKN23OriginalGraphBulkRows

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.SourceCollarBulk Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection

def tiltedForceConstant (power : ℕ) : ℝ :=
  2 * 2 ^ power * Real.sqrt (remainderAngularBoundConstant 3 power 0)

theorem actualRestrictedSourceFrames_tilted_bound (parameters : PhaseParameters)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ) :
    let row := completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters
      (by omega : power + 0 ≤ power + 1)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := power + 1) (cartesianSourceVector source)))
    ‖divisionHighWeight lower positive bounded (radialRowContraction lower positive power row)‖ ≤
      tiltedForceConstant power * ‖quotientEta parameters (power + 5) source‖ ∧
    ‖divisionHighWeight lower positive bounded (tangentialRowContraction lower positive power row)‖ ≤
      tiltedForceConstant power * ‖quotientEta parameters (power + 5) source‖ := by
  dsimp only
  rw [restrictionRow_core_grade_independent parameters (cartesianSourceVector source) lower positive bounded
    (by omega : power + 0 ≤ power + 1) (by omega : power + 0 ≤ power + 5)]
  have relation := sourceTiltRow_sameRestriction (grade := power + 5) (power := power)
    parameters (cartesianSourceVector source) flat.1 (by omega) lower positive bounded (by omega)
  have bound := sourceTiltRow_bound (grade := power + 5) (power := power)
    parameters (cartesianSourceVector source) flat.1 (by omega) lower positive bounded 0 (by omega)
  have original := originalPlanarCore_norm_le parameters (power + 5) source
  have total : 2 * 2 ^ power * ‖sourceTiltRow (grade := power + 5) (power := power)
      parameters (cartesianSourceVector source) flat.1 (by omega) lower positive bounded 0 (by omega)‖ ≤
      tiltedForceConstant power * ‖quotientEta parameters (power + 5) source‖ := by
    unfold tiltedForceConstant
    exact (mul_le_mul_of_nonneg_left (bound.trans (mul_le_mul_of_nonneg_left original (Real.sqrt_nonneg _)))
      (by positivity)).trans_eq (by ring)
  exact ⟨(actualTiltedRadial_bound positive bounded power _ _ relation).trans total,
    (actualTiltedTangential_bound positive bounded power _ _ relation).trans total⟩

theorem divisionHighWeight_s11 (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (annularS11RowValue lower field) =
      annularS11RowValue lower (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode]
  change _ = annularS11Ratio mode • divisionHighWeight lower positive bounded field mode
  rw [divisionHighWeight_mode]
  exact map_smul _ _ _

theorem actualOriginalF0Graph_tilted_coordinate_bound (parameters : PhaseParameters)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ‖divisionHighWeight lower positive bounded.le
      (annularSourceCoordinate parameters 1 lower 1 0 0
        (actualOriginalF0Graph parameters lower positive bounded grade source))‖ ≤
      tiltedForceConstant (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ := by
  rw [actualOriginalF0Graph_value, divisionHighWeight_s11]
  exact (annularS11RowValue_norm_le lower _).trans
    (actualRestrictedSourceFrames_tilted_bound parameters source flat lower positive bounded.le (grade + 1)).2

theorem actualOriginalF1Row_tilted_bound (parameters : PhaseParameters)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ) :
    ‖divisionHighWeight lower positive bounded
      (actualOriginalF1Row parameters lower positive bounded grade source)‖ ≤
      tiltedForceConstant (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ := by
  rw [actualOriginalF1Row_value, divisionHighWeight_lowering]
  exact (annularWeightLoweringRowValue_norm_le lower _).trans
    (actualRestrictedSourceFrames_tilted_bound parameters source flat lower positive bounded (grade + 1)).1

theorem actualOriginalF2Graph_tilted_coordinate_bound (parameters : PhaseParameters) (L : ℝ)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ‖divisionHighWeight lower positive bounded.le
      (annularSourceCoordinate parameters 1 lower 0 0 0
        (actualOriginalF2Graph parameters L lower positive bounded grade source))‖ ≤
      (|L⁻¹| * Real.sqrt (remainderAngularBoundConstant 3 grade 0)) *
        ‖quotientEta parameters (grade + 5) source‖ := by
  rw [actualOriginalF2Graph_value, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [restrictionRow_core_grade_independent parameters (source 3) lower positive bounded.le
    (by omega : grade + 0 ≤ grade + 1) (by omega : grade + 0 ≤ grade + 5)]
  have bound := originalTiltedRestriction_bound (grade := grade + 5) (power := grade)
    parameters (source 3) flat.2.2 (by omega) lower positive bounded.le (by omega)
  have original := originalScalarCore_norm_le parameters (grade + 5) source 3
  have paid := bound.trans (mul_le_mul_of_nonneg_left original (Real.sqrt_nonneg _))
  simpa only [abs_inv, mul_assoc] using mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr (abs_nonneg L))

end Grad.ExhaustionSourceAllocation
