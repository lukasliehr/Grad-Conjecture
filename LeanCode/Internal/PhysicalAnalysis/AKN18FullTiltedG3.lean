import AKN17ActualSourceProductBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.SourceCollarRestriction Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.Allocation Grad.AxisCore Grad.QuotientProjection

theorem divisionHighWeight_meanFree (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (meanFreeRow lower field) =
      meanFreeRow lower (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode, meanFreeRow_apply, meanFreeRow_apply]
  split_ifs
  · exact map_zero _
  · rfl

theorem actualFullCorrection_tilted_bound {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source) (paid : power + 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    ‖divisionHighWeight lower positive bounded
      (fullCorrectionRow (power := power) parameters L rho epsilon field small lower positive bounded
        (by omega) (quotientEta parameters grade source))‖ ≤
      (3 * tiltedCoefficientHighConstant parameters L power + tiltedDivisionConstant power L) *
        ‖quotientEta parameters grade source‖ +
      3 * tiltedCoefficientLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
        ‖quotientEta parameters 5 source‖ := by
  have first := actualCoefficientSourceProduct_tilted_bound parameters L rho epsilon field small source flat paid lower positive bounded 0
  have second := actualCoefficientSourceProduct_tilted_bound parameters L rho epsilon field small source flat paid lower positive bounded 1
  have third := actualCoefficientSourceProduct_tilted_bound parameters L rho epsilon field small source flat paid lower positive bounded 2
  have circle := actualDividedSourceRows_tilted_bound parameters L source flat paid lower positive bounded 1
  rw [fullCorrectionRow, divisionHighWeight_meanFree]
  simp only [map_sub (divisionHighWeight lower positive bounded), map_add (divisionHighWeight lower positive bounded)]
  exact (meanFreeRow_four_bound lower _ _ _ _).trans (by linarith only [first, second, third, circle])

theorem actualScalarG_tilted_bound {grade power : ℕ}
    (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (flat : SourceHigherVanishing source) (paid : power + 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    ‖divisionHighWeight lower positive bounded (scalarGRow (power := power) parameters L lower positive bounded
      (by omega) (quotientEta parameters grade source))‖ ≤
      (|L⁻¹| * Real.sqrt (remainderAngularBoundConstant 2 power 0)) * ‖quotientEta parameters grade source‖ := by
  have scalar := (originalTiltedRestriction_bound parameters (source 2) flat.2.1 (by omega : 2 + power + 2 ≤ grade)
      lower positive bounded le_rfl).trans
    (mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters grade source 2) (Real.sqrt_nonneg _))
  change ‖divisionHighWeight lower positive bounded ((L : ℂ)⁻¹ • completedRestrictionRow
    (power := power) (radial := 0) lower positive bounded parameters _
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (source 2))))‖ ≤ _
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
  exact (mul_le_mul_of_nonneg_left scalar (abs_nonneg L⁻¹)).trans_eq (by ring)

def tiltedG3HighConstant (parameters : PhaseParameters) (L : ℝ) (power : ℕ) : ℝ :=
  |L⁻¹| * Real.sqrt (remainderAngularBoundConstant 2 power 0) +
    3 * tiltedCoefficientHighConstant parameters L power + tiltedDivisionConstant power L

/-- SAME full G3, including its essential circular -F0/r correction and
all coefficient-created modes. Projection stays after the products. -/
theorem actualFullG3_tilted_bound {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source) (paid : power + 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    ‖divisionHighWeight lower positive bounded
      (fullG3Row (power := power) parameters L rho epsilon field small lower positive bounded
        (by omega) (quotientEta parameters grade source))‖ ≤
      tiltedG3HighConstant parameters L power * ‖quotientEta parameters grade source‖ +
      3 * tiltedCoefficientLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
        ‖quotientEta parameters 5 source‖ := by
  rw [fullG3Row, map_add]
  exact (norm_add_le _ _).trans ((add_le_add
    (actualScalarG_tilted_bound parameters L source flat paid lower positive bounded)
    (actualFullCorrection_tilted_bound parameters L rho epsilon field small source flat paid lower positive bounded)).trans_eq
      (by unfold tiltedG3HighConstant; ring))

end Grad.ExhaustionSourceAllocation
