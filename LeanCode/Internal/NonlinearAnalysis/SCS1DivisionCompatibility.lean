import SCC34PublicCoefficientBoundary
import SRC10ExactSourceDomains

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarAngular

/-- The same divided field, not two independently chosen weighted rows. -/
theorem completedDivisionRow_compatible {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 0 + 3 ≤ grade)
    (field : AGrade parameters dimension grade) :
    RadialRowsCompatible lower power
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid field)
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega) field) := by
  intro mode
  rw [completedDivisionRow_literal, completedDivisionRow_literal]
  simp only [pow_zero, one_smul]

theorem completedDivisionRow_inclusion {dimension low high power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ low) (grades : low ≤ high) :
    (completedDivisionRow (dimension := dimension) (power := power) (radial := radial)
      lower positive bounded parameters paid).comp (completedInclusion parameters grades) =
      completedDivisionRow (power := power) (radial := radial) lower positive bounded parameters (paid.trans grades) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro core
  rw [ContinuousLinearMap.comp_apply, completedInclusion_apply_eta,
    completedDivisionRow_core, completedDivisionRow_core]
  rfl

/-- The low branch uses exactly the original grade three, independently of
the high source grade used for the same field. -/
theorem completedDivisionRow_low_bound {dimension grade : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) :
    ‖completedDivisionRow (power := 0) (radial := 0) lower positive bounded parameters large field‖ ≤
      Real.sqrt (finiteAngularBoundConstant 0 0) * ‖completedInclusion parameters large field‖ := by
  have factor := DFunLike.congr_fun
    (completedDivisionRow_inclusion (dimension := dimension) (power := 0) (radial := 0)
      lower positive bounded parameters (by omega : 0 + 0 + 3 ≤ 3) large) field
  rw [← factor]
  exact completedDivisionRow_bound lower positive bounded parameters (by omega) _

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.valueMap {sourceDimension targetDimension power : ℕ}
    {lower : ℝ} {high low : DivisionRow sourceDimension lower}
    (compatible : RadialRowsCompatible lower power high low)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    RadialRowsCompatible lower power (divisionRowValueMap lower mapping high)
      (divisionRowValueMap lower mapping low) := by
  intro mode
  rw [divisionRowValueMap_apply, divisionRowValueMap_apply, compatible mode, map_smul]

theorem annularShiftScalar_weight (power : ℕ) (shift : ℤ) (mode : ℤ × ℤ) :
    annularShiftScalar power shift mode * (annularFrequency (mode.1 - shift) mode.2 : ℂ) ^ power =
      (annularFrequency mode.1 mode.2 : ℂ) ^ power := by
  have nonzero : (annularFrequency (mode.1 - shift) mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (annularFrequency_pos _ _).ne'
  simp only [annularShiftScalar, Complex.ofReal_pow, Complex.ofReal_div, div_pow]
  exact div_mul_cancel₀ _ (pow_ne_zero _ nonzero)

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.shift {dimension power : ℕ} {lower : ℝ}
    {high low : DivisionRow dimension lower}
    (compatible : RadialRowsCompatible lower power high low) (shift : ℤ) :
    RadialRowsCompatible lower power (annularRowShift lower power shift high)
      (annularRowShift lower 0 shift low) := by
  intro mode
  rw [annularRowShift_apply, annularRowShift_apply, compatible, smul_smul,
    annularShiftScalar_weight]
  simp only [annularShiftScalar, pow_zero, Complex.ofReal_one, one_smul]

end Grad.SourceCollarFullSource
