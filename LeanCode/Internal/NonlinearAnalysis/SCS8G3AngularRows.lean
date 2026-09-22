import SCS7FullG3Row

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.ConstrainedGrades Grad.AxisCore
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.SourceCollarBulk Grad.GaugeCoefficients.Physical.Allocation

variable {grade order : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
  (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (paid : order + 4 ≤ grade)
  (source : ZAmbient parameters grade)

/-- The value and angular derivative share one actual strong G3 row.
The two exact diagonal multipliers remove precisely one power of nu. -/
def g3ValueRow : DivisionRow 1 lower :=
  annularWeightLoweringRowValue lower
    (fullG3Row (power := order + 1) parameters L rho epsilon field small lower positive bounded (by omega) source)

def g3AngularRow : DivisionRow 1 lower :=
  annularAngularRow lower
    (fullG3Row (power := order + 1) parameters L rho epsilon field small lower positive bounded (by omega) source)

def g3HighConstant (parameters : PhaseParameters) (L : ℝ) (order : ℕ) : ℝ :=
  |L⁻¹| * Real.sqrt (restrictionRowConstant (order + 1) 0) +
    3 * coefficientSourceHighConstant parameters L (order + 1) + sourceDivisionConstant (order + 1) L

def g3LowConstant (parameters : PhaseParameters) (L : ℝ) (order : ℕ) : ℝ :=
  3 * coefficientSourceLowConstant parameters L (order + 1)

theorem g3ValueRow_bound :
    ‖g3ValueRow parameters L rho epsilon field small lower positive bounded paid source‖ ≤
      g3HighConstant parameters L order * ‖source‖ +
        g3LowConstant parameters L order * physicalBudget parameters field rho epsilon (order + 6) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ :=
  (annularWeightLoweringRowValue_norm_le lower _).trans
    (fullG3Row_bound (power := order + 1) parameters L rho epsilon field small lower positive bounded (by omega) source)

theorem g3AngularRow_bound :
    ‖g3AngularRow parameters L rho epsilon field small lower positive bounded paid source‖ ≤
      g3HighConstant parameters L order * ‖source‖ +
        g3LowConstant parameters L order * physicalBudget parameters field rho epsilon (order + 6) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ :=
  (annularAngularRowValue_norm_le lower _).trans
    (fullG3Row_bound (power := order + 1) parameters L rho epsilon field small lower positive bounded (by omega) source)

/-- No derivative slot is independent: RG3 is precisely i m times G3
on every cell, as an equality in the original completed radial L2. -/
theorem g3AngularRow_mode (mode : ℤ × ℤ) :
    g3AngularRow parameters L rho epsilon field small lower positive bounded paid source mode =
      (Complex.I * (mode.1 : ℂ)) •
        g3ValueRow parameters L rho epsilon field small lower positive bounded paid source mode := by
  change annularAngularRatio mode • _ =
    (Complex.I * (mode.1 : ℂ)) • (annularWeightLoweringRatio mode • _)
  rw [smul_smul]
  rfl

theorem g3AngularRow_literal :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters order lower
        (g3AngularRow parameters L rho epsilon field small lower positive bounded paid source) radius mode =
      (Complex.I * (mode.1 : ℂ)) • originalRowCoefficient parameters order lower
        (g3ValueRow parameters L rho epsilon field small lower positive bounded paid source) radius mode := by
  apply ae_all_iff.mpr
  intro mode
  have pointwise := Lp.coeFn_smul (Complex.I * (mode.1 : ℂ))
    (g3ValueRow parameters L rho epsilon field small lower positive bounded paid source mode)
  rw [← g3AngularRow_mode parameters L rho epsilon field small lower positive bounded paid source mode] at pointwise
  filter_upwards [pointwise] with radius same
  unfold originalRowCoefficient
  rw [same]
  exact smul_comm ((originalRowWeight parameters order radius mode : ℂ)⁻¹)
    (Complex.I * (mode.1 : ℂ))
    (g3ValueRow parameters L rho epsilon field small lower positive bounded paid source mode radius)

end Grad.SourceCollarFullSource
