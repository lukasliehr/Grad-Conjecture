import SCC7ActualSignedCofactor
import GQC8ActualSmoothCoefficient
import GC18APProduct
import RSC1PolarDensity

noncomputable section
open scoped BigOperators ENNReal

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The literal cellwise AP8 budget, retaining its summability in the cell.
No individual cell is bounded by a global constant before summation. -/
def coefficientCellBudget {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) (cell : ℤ) : ℝ :=
  ∑ index : DerivativeIndex grade, ‖coefficient.val (cell, index)‖

theorem coefficientCellBudget_nonnegative {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) (cell : ℤ) :
    0 ≤ coefficientCellBudget coefficient cell :=
  Finset.sum_nonneg (fun index _ => norm_nonneg (coefficient.val (cell, index)))

theorem coefficientCellBudget_summable {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) :
    Summable (coefficientCellBudget coefficient) := by
  have summable : Summable (fun pair : ℤ × DerivativeIndex grade => ‖coefficient.val pair‖) := by
    simpa using (lp.memℓp coefficient.val).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  change Summable (fun cell => ∑ index : DerivativeIndex grade, ‖coefficient.val (cell, index)‖)
  simpa only [tsum_fintype] using summable.prod

theorem coefficientCellBudget_tsum {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) :
    ∑' cell, coefficientCellBudget coefficient cell = ‖coefficient‖ :=
  (coefficient_norm_formula grade input output coefficient).symm

theorem coefficient_scaled_point_norm {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade cell index point *
      ‖coefficientDerivative coefficient cell index point‖ ≤ ‖coefficient.val (cell, index)‖ := by
  have literal := weighted_derivative_literal grade input output coefficient cell index point
  have positive := coefficientScale_pos L sigma gamma ell grade cell index point
  have estimate := (coefficient.val (cell, index)).norm_coe_le_norm point
  rw [show coefficient.val (cell, index) point = _ from literal, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive] at estimate
  exact estimate

theorem coefficient_scaled_column_norm {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk)
    (column : PhysicalValue input) :
    coefficientScale L sigma gamma ell grade cell index point *
      ‖coefficientDerivative coefficient cell index point column‖ ≤
      coefficientCellBudget coefficient cell * ‖column‖ := by
  have term : ‖coefficient.val (cell, index)‖ ≤ coefficientCellBudget coefficient cell :=
    Finset.single_le_sum (f := fun index => ‖coefficient.val (cell, index)‖)
      (fun index _ => norm_nonneg (coefficient.val (cell, index))) (Finset.mem_univ index)
  calc
    _ ≤ coefficientScale L sigma gamma ell grade cell index point *
        (‖coefficientDerivative coefficient cell index point‖ * ‖column‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
        (coefficientScale_pos L sigma gamma ell grade cell index point).le
    _ ≤ ‖coefficient.val (cell, index)‖ * ‖column‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (coefficient_scaled_point_norm coefficient cell index point) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right term (norm_nonneg _)

theorem unit_scaledCellWeight (cell : ℤ) : scaledCellWeight 1 1 cell = cellFrequency cell := by
  simp [scaledCellWeight, cellFrequency_formula]

/-- Genuine all-order cell jet, reconstructed from the same coherent family. -/
def coefficientColumnJet {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input) : ClosedJet output :=
  operatorJetColumn (actualCoefficientJet (unitDiskAdmissible parameters) family coherent cell) column

theorem coefficientColumnJet_derivative {input output grade : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    closedMultiDerivative (coefficientColumnJet parameters family coherent cell column)
      (derivativeMultiIndex index) point = coefficientDerivative (family grade) cell index point column := by
  rw [coefficientColumnJet, operatorJetColumn_multi, actualCoefficientJet_coherent]

theorem coefficientColumnJet_density_bound {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) (cell : ℤ) (column : PhysicalValue input)
    (point : ClosedDisk) :
    originalEnvelope parameters.sigma0 parameters.gamma 1 cell point.val ^ 2 *
      cartesianPointDensity (cellFrequency cell) grade
        (coefficientColumnJet parameters family coherent cell column) point ≤
      (Fintype.card (GradeMultiIndex grade) : ℝ) *
        (coefficientCellBudget (family grade) cell * ‖column‖) ^ 2 := by
  rw [cartesianPointDensity, Finset.mul_sum]
  calc
    _ ≤ ∑ _index : GradeMultiIndex grade,
        (coefficientCellBudget (family grade) cell * ‖column‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro index _
      have bound := coefficient_scaled_column_norm (family grade) cell index point column
      have squared := pow_le_pow_left₀
        (mul_nonneg (coefficientScale_pos 1 parameters.sigma0 parameters.gamma 1 grade cell index point).le
          (norm_nonneg _)) bound 2
      change originalEnvelope parameters.sigma0 parameters.gamma 1 cell point.val ^ 2 *
        (cellFrequency cell ^ (2 * (grade - derivativeOrder index)) *
          ‖closedMultiDerivative (coefficientColumnJet parameters family coherent cell column)
            (derivativeMultiIndex index) point‖ ^ 2) ≤ _
      rw [coefficientColumnJet_derivative]
      simpa only [coefficientScale, unit_scaledCellWeight, mul_pow, ← pow_mul,
        Nat.mul_comm, mul_assoc] using squared
    _ = _ := by simp

end Grad.SourceCollarCoefficients
