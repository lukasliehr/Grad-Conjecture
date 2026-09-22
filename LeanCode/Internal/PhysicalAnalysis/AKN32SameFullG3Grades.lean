import AKN31SamePrimitiveSourceGrades
import SCS40PhysicalG3Coefficients

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate

theorem row_inserted_of_originalCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (lower : ℝ) (positive : 0 < lower) (high low : DivisionRow dimension lower)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters grade lower high radius mode =
        originalRowCoefficient parameters 0 lower low radius mode) (mode : ℤ × ℤ) :
    high mode = annularFrequency mode.1 mode.2 ^ grade • low mode := by
  apply Lp.ext
  filter_upwards [same, Lp.coeFn_smul (annularFrequency mode.1 mode.2 ^ grade) (low mode),
    ae_restrict_mem measurableSet_Icc] with radius same scalar inside
  rw [scalar, ← originalRowCoefficient_weighted parameters grade lower high radius
    (positive.trans_le inside.1) mode, same mode]
  have weight : originalRowWeight parameters grade radius mode =
      annularFrequency mode.1 mode.2 ^ grade * originalRowWeight parameters 0 radius mode := by
    unfold originalRowWeight
    simp only [pow_zero, mul_one]
    ring
  rw [weight, Complex.ofReal_mul, mul_smul, originalRowCoefficient_weighted parameters 0 lower low radius
    (positive.trans_le inside.1) mode, Complex.coe_smul]
  rfl

/-- The SCS full source at every input grade decodes to the same actual
physical G3, including the original projected circle correction. -/
theorem actualG3Value_same_physical (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters grade lower
        (g3ValueRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
          (quotientEta parameters (grade + 6) source)) radius mode =
      doubleCoefficient (physicalG3 parameters L epsilon field source radius (positive.le.trans inside.1) inside.2) mode := by
  have division := originalFlatSource_division_inputs parameters (by omega : 3 ≤ grade + 6) source flat
  filter_upwards [g3Rows_actual_coefficients parameters L rho epsilon field small
    (by omega : grade + 4 ≤ grade + 6) lower positive bounded
    (quotientEta parameters (grade + 6) source) division.1 division.2] with radius actual
  intro inside mode
  exact (actual inside mode).1.trans (actualG3Coefficient_physical parameters L rho epsilon field small
    source radius (positive.le.trans inside.1) inside.2 (by omega : 3 ≤ grade + 6) mode)

theorem actualG3Value_inserted (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (mode : ℤ × ℤ) :
    g3ValueRow (order := grade) parameters L rho epsilon field small lower positive bounded (by omega)
      (quotientEta parameters (grade + 6) source) mode =
    annularFrequency mode.1 mode.2 ^ grade •
      g3ValueRow (order := 0) parameters L rho epsilon field small lower positive bounded (by norm_num)
        (quotientEta parameters 6 source) mode := by
  apply row_inserted_of_originalCoefficient parameters grade lower positive _ _ _ mode
  filter_upwards [actualG3Value_same_physical parameters L rho epsilon field small lower positive bounded grade source flat,
    actualG3Value_same_physical parameters L rho epsilon field small lower positive bounded 0 source flat,
    ae_restrict_mem measurableSet_Icc] with radius high low inside
  intro other
  exact (high inside other).trans (low inside other).symm

theorem actualOriginalG3Row_inserted (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (mode : ℤ × ℤ) :
    actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source mode =
      annularFrequency mode.1 mode.2 ^ grade •
        actualOriginalG3Row parameters L rho epsilon field small lower positive bounded 0 source mode := by
  rw [actualOriginalG3Row, strengthenedG_mode lower _ _
    (fun other => g3AngularRow_mode parameters L rho epsilon field small lower positive bounded (by omega) _ other),
    actualOriginalG3Row, strengthenedG_mode lower _ _
    (fun other => g3AngularRow_mode parameters L rho epsilon field small lower positive bounded (by omega) _ other),
    actualG3Value_inserted parameters L rho epsilon field small lower positive bounded grade source flat mode]
  exact smul_comm _ _ _

end Grad.ExhaustionSourceAllocation
