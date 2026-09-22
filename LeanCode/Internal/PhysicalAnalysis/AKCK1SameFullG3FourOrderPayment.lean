import AKCI6ActualBalancedSystemOneOrder
import SCS40PhysicalG3Coefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.SourceCollarBulk
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual full G3 at power q+1 is paid at original source grade q+4.
The high coefficient uses the independently lowered original source at grade3. -/
theorem actualFullG3_fourPayment (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    ‖fullG3Row (power := grade+1) parameters length rho epsilon field small lower positive bounded
      (by omega : grade+1+3 ≤ grade+4) (quotientEta parameters (grade+4) source)‖ ≤
      g3HighConstant parameters length grade * ‖quotientEta parameters (grade+4) source‖ +
        g3LowConstant parameters length grade * physicalBudget parameters field rho epsilon (grade+6) *
          ‖quotientEta parameters 3 source‖ := by
  have actual := fullG3Row_bound (power := grade+1) parameters length rho epsilon field small lower positive bounded
    (by omega : grade+1+3 ≤ grade+4) (quotientEta parameters (grade+4) source)
  rw [zLowering_core] at actual
  simpa only [g3HighConstant,g3LowConstant,show grade+1+5=grade+6 by omega] using actual

/-- The sharply paid row is the SAME full original physical G3, including
all kappa products, the circle correction and the original mean projection. -/
theorem actualFullG3_fourPayment_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters (grade+1) lower
        (fullG3Row (power := grade+1) parameters length rho epsilon field small lower positive bounded
          (by omega : grade+1+3 ≤ grade+4) (quotientEta parameters (grade+4) source)) radius mode =
        doubleCoefficient (physicalG3 parameters length epsilon field source radius
          (positive.le.trans inside.1) inside.2) mode := by
  have inputs := originalFlatSource_division_inputs parameters (by omega : 3≤grade+4) source flat
  filter_upwards [fullG3Row_actual_coefficient parameters length rho epsilon field small
    (by omega : 3≤grade+4) (quotientEta parameters (grade+4) source)
    (power := grade+1) (by omega) lower positive bounded inputs.1 inputs.2] with radius actual
  intro inside mode
  exact (actual inside mode).trans (actualG3Coefficient_physical parameters length rho epsilon field small
    source radius (positive.le.trans inside.1) inside.2 (by omega : 3≤grade+4) mode)

end Grad.OriginalCartesianTameEstimate
