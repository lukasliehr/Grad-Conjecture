import SM11AmbientReality

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.SmoothingFamily

open Grad.CartesianState

/-- The literal M16 weight, at the original fixed cell width. -/
def axisWeight (width : ℝ) (grade : ℕ) (cell : ℤ) : ℝ :=
  Real.exp (width * cellFrequency cell) * cellFrequency cell ^ grade

theorem axisWeight_pos (width : ℝ) (grade : ℕ) (cell : ℤ) : 0 < axisWeight width grade cell :=
  mul_pos (Real.exp_pos _) (pow_pos (cellFrequency_pos cell) _)

/-- Weighted coordinates; `axisCoefficient` removes precisely the M16 weight. -/
abbrev TGrade (_width : ℝ) (Value : Type*) [NormedAddCommGroup Value] (_grade : ℕ) :=
  lp (fun _ : ℤ => Value) 2

def axisCoefficient {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (field : TGrade width Value grade) (cell : ℤ) : Value :=
  ((axisWeight width grade cell : ℂ)⁻¹) • field cell

theorem axis_weighted_coefficient {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (field : TGrade width Value grade) (cell : ℤ) :
    (axisWeight width grade cell : ℂ) • axisCoefficient width grade field cell = field cell := by
  exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos width grade cell).ne') _

theorem axis_norm_sq {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (field : TGrade width Value grade) :
    ‖field‖ ^ 2 = ∑' cell : ℤ, Real.exp (2 * width * cellFrequency cell) *
      cellFrequency cell ^ (2 * grade) * ‖axisCoefficient width grade field cell‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext cell
  rw [← axis_weighted_coefficient width grade field cell, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (axisWeight_pos width grade cell)]
  have exponential : Real.exp (2 * width * cellFrequency cell) =
      Real.exp (width * cellFrequency cell) ^ 2 := by
    rw [show 2 * width * cellFrequency cell = width * cellFrequency cell + width * cellFrequency cell by ring,
      Real.exp_add, pow_two]
  rw [exponential, axisWeight]
  ring

def axisCoreSubmodule (width : ℝ) (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :
    Submodule ℂ (ℤ → Value) where
  carrier values := ∀ grade : ℕ, Memℓp (fun cell => (axisWeight width grade cell : ℂ) • values cell) 2
  zero_mem' := by
    intro grade
    convert (zero_memℓp : Memℓp (0 : ℤ → Value) 2) using 1
    funext cell
    exact smul_zero _
  add_mem' := by
    intro first second firstMember secondMember grade
    convert (firstMember grade).add (secondMember grade) using 1
    funext cell
    exact smul_add _ _ _
  smul_mem' := by
    intro scalar values member grade
    convert (member grade).const_smul scalar using 1
    funext cell
    exact smul_comm _ _ _

abbrev AxisCore (width : ℝ) (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :=
  axisCoreSubmodule width Value

def axisToGrade {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) : AxisCore width Value →ₗ[ℂ] TGrade width Value grade where
  toFun values := ⟨fun cell => (axisWeight width grade cell : ℂ) • values.1 cell, values.property grade⟩
  map_add' first second := by apply Subtype.ext; funext cell; exact smul_add _ _ _
  map_smul' scalar values := by apply Subtype.ext; funext cell; exact smul_comm _ _ _

theorem axisToGrade_coefficient {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (values : AxisCore width Value) (cell : ℤ) :
    axisCoefficient width grade (axisToGrade width grade values) cell = values.1 cell := by
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos width grade cell).ne') _

theorem axisToGrade_injective {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) : Function.Injective (axisToGrade (Value := Value) width grade) := by
  intro first second equality
  apply Subtype.ext
  funext cell
  rw [← axisToGrade_coefficient width grade first cell, equality, axisToGrade_coefficient]

theorem axisToGrade_norm_sq {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (values : AxisCore width Value) :
    ‖axisToGrade width grade values‖ ^ 2 = ∑' cell : ℤ, Real.exp (2 * width * cellFrequency cell) *
      cellFrequency cell ^ (2 * grade) * ‖values.1 cell‖ ^ 2 := by
  simpa only [axisToGrade_coefficient] using axis_norm_sq width grade (axisToGrade width grade values)

theorem axis_weighted_norm {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (grade : ℕ) (values : AxisCore width Value) (cell : ℤ) :
    ‖axisToGrade width grade values cell‖ = axisWeight width grade cell * ‖values.1 cell‖ := by
  change ‖(axisWeight width grade cell : ℂ) • values.1 cell‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (axisWeight_pos width grade cell)]

def boundedAxisMultiplier {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (factor : ℤ → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (factorBound : ∀ cell, ‖factor cell‖ ≤ bound) : AxisCore width Value →ₗ[ℂ] AxisCore width Value where
  toFun values := ⟨fun cell => (factor cell : ℂ) • values.1 cell, by
    intro grade
    apply Memℓp.mono' ((values.property grade).const_smul (bound : ℂ))
    intro cell
    change ‖(axisWeight width grade cell : ℂ) • ((factor cell : ℂ) • values.1 cell)‖ ≤
      ‖(bound : ℂ) • ((axisWeight width grade cell : ℂ) • values.1 cell)‖
    rw [smul_comm (axisWeight width grade cell : ℂ) (factor cell : ℂ)]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg boundNonnegative]
    exact mul_le_mul_of_nonneg_right (factorBound cell) (mul_nonneg (abs_nonneg _) (norm_nonneg _))⟩
  map_add' first second := by apply Subtype.ext; funext cell; exact smul_add _ _ _
  map_smul' scalar values := by apply Subtype.ext; funext cell; exact smul_comm _ _ _

theorem axis_norm_le_of_weighted_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (width : ℝ) (first second : AxisCore width Value) (firstGrade secondGrade : ℕ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ cell, cellFrequency cell ^ firstGrade * ‖first.1 cell‖ ≤
      bound * (cellFrequency cell ^ secondGrade * ‖second.1 cell‖)) :
    ‖axisToGrade width firstGrade first‖ ≤ bound * ‖axisToGrade width secondGrade second‖ := by
  have comparison := lp.norm_mono (p := 2) (by norm_num)
    (x := axisToGrade width firstGrade first) (y := (bound : ℂ) • axisToGrade width secondGrade second) (by
      intro cell
      rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg boundNonnegative, axis_weighted_norm, axis_weighted_norm]
      simpa only [axisWeight, mul_assoc, mul_left_comm bound] using
        mul_le_mul_of_nonneg_left (pointwise cell) (Real.exp_pos (width * cellFrequency cell)).le)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg boundNonnegative] using comparison

end Grad.SmoothingFamily
