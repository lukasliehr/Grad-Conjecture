import SCS6CoefficientSourceProducts

noncomputable section
set_option maxHeartbeats 400000
open Set MeasureTheory
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.ConstrainedGrades Grad.AxisCore
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

variable {grade power : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
  (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (paid : power + 3 ≤ grade)
  (source : ZAmbient parameters grade)

def coefficientSourceProduct (component : Fin 3) : DivisionRow 1 lower :=
  (exists_dividedCoefficientProduct parameters L rho epsilon field small lower positive bounded paid source component).choose

theorem coefficientSourceProduct_bound (component : Fin 3) :
    ‖coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source component‖ ≤
      coefficientSourceHighConstant parameters L power * ‖source‖ +
        coefficientSourceLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ :=
  (exists_dividedCoefficientProduct parameters L rho epsilon field small lower positive bounded paid source component).choose_spec.1

theorem coefficientSourceProduct_literal (component : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      HasSum (fun shift : ℤ × ℤ => kappaScalar parameters L rho epsilon field small component 0 radius shift •
        originalRowCoefficient parameters 0 lower
          (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega) source component)
          radius (mode - shift))
        (originalRowCoefficient parameters power lower
          (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source component)
          radius mode) :=
  (exists_dividedCoefficientProduct parameters L rho epsilon field small lower positive bounded paid source component).choose_spec.2

/-- Full BS30 correction. The circle term is -F0/r, not zero. The mean-free
projection is applied only after all actual coefficient products are added. -/
def fullCorrectionRow : DivisionRow 1 lower :=
  meanFreeRow lower
    (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 0 +
      coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 1 -
      coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 2 -
      dividedSourceRows lower positive bounded parameters L paid source 1)

theorem fullCorrectionRow_bound :
    ‖fullCorrectionRow parameters L rho epsilon field small lower positive bounded paid source‖ ≤
      (3 * coefficientSourceHighConstant parameters L power + sourceDivisionConstant power L) * ‖source‖ +
        3 * coefficientSourceLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ := by
  have first := coefficientSourceProduct_bound parameters L rho epsilon field small lower positive bounded paid source 0
  have second := coefficientSourceProduct_bound parameters L rho epsilon field small lower positive bounded paid source 1
  have third := coefficientSourceProduct_bound parameters L rho epsilon field small lower positive bounded paid source 2
  have circle := dividedSourceRows_bound lower positive bounded parameters L paid source 1
  have triangle := meanFreeRow_four_bound lower
    (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 0)
    (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 1)
    (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 2)
    (dividedSourceRows lower positive bounded parameters L paid source 1)
  exact triangle.trans (by linarith only [first, second, third, circle])

def scalarGRow : DivisionRow 1 lower :=
  (L : ℂ)⁻¹ • completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters
    (show power + 0 ≤ grade by omega) (source 2)

theorem scalarGRow_bound :
    ‖scalarGRow parameters L lower positive bounded paid source‖ ≤
      (|L⁻¹| * Real.sqrt (restrictionRowConstant power 0)) * ‖source‖ := by
  unfold scalarGRow
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
  have bound := (completedRestrictionRow_bound (power := power) (radial := 0) lower positive bounded parameters
    (show power + 0 ≤ grade by omega) (source 2)).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le source 2) (Real.sqrt_nonneg _))
  exact (mul_le_mul_of_nonneg_left bound (abs_nonneg L⁻¹)).trans_eq (by ring)

def fullG3Row : DivisionRow 1 lower :=
  scalarGRow parameters L lower positive bounded paid source +
    fullCorrectionRow parameters L rho epsilon field small lower positive bounded paid source

theorem fullG3Row_bound :
    ‖fullG3Row parameters L rho epsilon field small lower positive bounded paid source‖ ≤
      (|L⁻¹| * Real.sqrt (restrictionRowConstant power 0) +
        3 * coefficientSourceHighConstant parameters L power + sourceDivisionConstant power L) * ‖source‖ +
        3 * coefficientSourceLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ := by
  exact (norm_add_le _ _).trans ((add_le_add
    (scalarGRow_bound parameters L lower positive bounded paid source)
    (fullCorrectionRow_bound parameters L rho epsilon field small lower positive bounded paid source)).trans_eq (by ring))

end Grad.SourceCollarFullSource
