import AxisThirteenBound
import AX2AxisCore

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### The axis-core carrier and its weight

The target is the generic axis carrier `Grad.AxisCore.axisCoreSubmodule`
with its `axisEta` grade norms. Its weight is definitionally
`Grad.AxisSplit.axisWeight`. -/

theorem axisCoreWeight_eq : @Grad.AxisCore.axisWeight = @Grad.AxisSplit.axisWeight := rfl

/-! ### The two summation lemmas between the state and axis carriers -/

/-- A coordinatewise domination of the weighted axis coordinates by one
grade row sums to the `T`-norm against `A`-norm bound. -/
theorem axisEta_le_of_row {valueDimension rowDimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters valueDimension) (grade : ℕ)
    (bound : ℝ) (boundNonneg : 0 ≤ bound) (field : ACore parameters rowDimension)
    (rowGrade : ℕ)
    (dominated : ∀ cell : ℤ,
      axisWeight parameters grade cell * ‖family.val cell‖ ≤
        bound * ‖cellGradeRowLinear (grade := rowGrade) parameters cell (field.val cell)‖) :
    ‖Grad.AxisCore.axisEta parameters valueDimension grade family‖ ≤
      bound * originalGradeNorm rowGrade field := by
  set rowNorms : lp (fun _ : ℤ => ℝ) 2 :=
    ⟨fun cell => ‖rawCartesianGradeCoordinates parameters rowGrade field.val cell‖,
      (field.property rowGrade).norm⟩ with rowNormsDef
  have rowEq : ‖rowNorms‖ = originalGradeNorm rowGrade field := by
    rw [originalGradeNorm_eq_lp field rowGrade, rowNormsDef]
    exact lp_norm_of_norms
      (⟨rawCartesianGradeCoordinates parameters rowGrade field.val,
        field.property rowGrade⟩ :
        lp (fun _ : ℤ => CartesianGradeRow rowDimension rowGrade) 2)
  have majorantNorm : ‖(bound : ℝ) • rowNorms‖ ≤ bound * originalGradeNorm rowGrade field := by
    rw [norm_smul, Real.norm_of_nonneg boundNonneg, rowEq]
  apply le_trans _ majorantNorm
  apply lp.norm_mono (by norm_num)
  intro cell
  have coordinateNorm :
      ‖(Grad.AxisCore.axisEta parameters valueDimension grade family) cell‖ =
        axisWeight parameters grade cell * ‖family.val cell‖ := by
    rw [Grad.AxisCore.axisEta_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Grad.AxisCore.axisWeight_pos parameters grade cell)]
    rfl
  change ‖(Grad.AxisCore.axisEta parameters valueDimension grade family) cell‖ ≤ _
  rw [coordinateNorm]
  apply le_trans (dominated cell)
  have valueForm : ((bound : ℝ) • rowNorms).val cell =
      bound * ‖rawCartesianGradeCoordinates parameters rowGrade field.val cell‖ := rfl
  have rowForm : bound *
      ‖cellGradeRowLinear (grade := rowGrade) parameters cell (field.val cell)‖ =
      ((bound : ℝ) • rowNorms).val cell := by
    rw [valueForm, raw_norm_eq_row]
  rw [rowForm]
  exact le_abs_self _

/-- A coordinatewise domination of the grade rows by weighted axis
coordinates sums to the `A`-norm against `T`-norm bound. -/
theorem originalGradeNorm_le_of_axis_row {valueDimension rowDimension : ℕ}
    (field : ACore parameters rowDimension) (grade : ℕ) (bound : ℝ)
    (boundNonneg : 0 ≤ bound)
    (family : Grad.AxisCore.AxisSmoothCore parameters valueDimension) (etaGrade : ℕ)
    (dominated : ∀ cell : ℤ,
      ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ≤
        bound * (axisWeight parameters etaGrade cell * ‖family.val cell‖)) :
    originalGradeNorm grade field ≤
      bound * ‖Grad.AxisCore.axisEta parameters valueDimension etaGrade family‖ := by
  have majorantNorm :
      ‖(bound : ℂ) • Grad.AxisCore.axisEta parameters valueDimension etaGrade family‖ =
        bound * ‖Grad.AxisCore.axisEta parameters valueDimension etaGrade family‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg boundNonneg]
  rw [originalGradeNorm_eq_lp field grade, ← majorantNorm]
  apply lp.norm_mono (by norm_num)
  intro cell
  change ‖rawCartesianGradeCoordinates parameters grade field.val cell‖ ≤ _
  rw [raw_norm_eq_row]
  apply le_trans (dominated cell)
  have valueForm :
      ((bound : ℂ) • Grad.AxisCore.axisEta parameters valueDimension etaGrade family) cell =
        (bound : ℂ) •
          (Grad.AxisCore.axisEta parameters valueDimension etaGrade family) cell := by
    rw [lp.coeFn_smul]
    rfl
  have coordinateNorm :
      ‖((bound : ℂ) • Grad.AxisCore.axisEta parameters valueDimension etaGrade family) cell‖ =
        bound * (axisWeight parameters etaGrade cell * ‖family.val cell‖) := by
    rw [valueForm, norm_smul, Complex.norm_real, Real.norm_of_nonneg boundNonneg,
      Grad.AxisCore.axisEta_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Grad.AxisCore.axisWeight_pos parameters etaGrade cell)]
    rfl
  rw [coordinateNorm]

/-! ### All-grade row domination of the axis value and gradient -/

/-- The value trace against the two-shifted row, at every grade. -/
theorem trace_value_row_bound {dimension : ℕ} (field : ClosedJet dimension) (cell : ℤ)
    (grade : ℕ) :
    axisWeight parameters grade cell * ‖originValue field‖ ≤
      6 * Grad.CartesianState.diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
  rcases Nat.eq_zero_or_pos grade with gradeZero | gradePositive
  · subst gradeZero
    apply le_trans (mul_le_mul_of_nonneg_right
      (axisWeight_mono parameters zero_le_one cell) (norm_nonneg _))
    exact sharp_cell_value_trace parameters field cell 1 le_rfl
  · apply le_trans (sharp_cell_value_trace parameters field cell grade gradePositive)
    apply mul_le_mul_of_nonneg_left (row_mono parameters cell field (by omega))
    exact mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le

/-- The gradient trace against the three-shifted row, at every grade. -/
theorem trace_gradient_row_bound {dimension : ℕ} (field : ClosedJet dimension)
    (cell : ℤ) (grade : ℕ) (direction : Fin 2) :
    axisWeight parameters grade cell * ‖originPartial direction field‖ ≤
      6 * Grad.CartesianState.diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ := by
  rcases Nat.eq_zero_or_pos grade with gradeZero | gradePositive
  · subst gradeZero
    apply le_trans (mul_le_mul_of_nonneg_right
      (axisWeight_mono parameters zero_le_one cell) (norm_nonneg _))
    exact sharp_cell_gradient_trace parameters field cell 1 le_rfl direction
  · apply le_trans (sharp_cell_gradient_trace parameters field cell grade
      gradePositive direction)
    apply mul_le_mul_of_nonneg_left (row_mono parameters cell field (by omega))
    exact mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le

/-! ### The trace maps `J0` and `J_i` into the accepted axis core -/

/-- The axis value family of a state-core field is in the accepted axis core. -/
theorem traceValue_mem {dimension : ℕ} (field : ACore parameters dimension) :
    (fun cell => originValue (field.val cell)) ∈
      Grad.AxisCore.axisCoreSubmodule parameters dimension := by
  intro grade
  have rowSummable : Summable (fun cell : ℤ =>
      ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ ^ 2) := by
    have memberRow := row_norm_memlp field (grade + 2)
    have squares := (memlp_iff_summable_sq (fun cell =>
      ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖)).mp
      memberRow
    apply squares.congr
    intro cell
    rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply Summable.of_nonneg_of_le (fun cell => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun cell => ?_)
    (rowSummable.mul_left ((6 * Grad.CartesianState.diskSupConstant) ^ 2))
  have linear := trace_value_row_bound (parameters := parameters) (field.val cell)
    cell grade
  have squared := pow_le_pow_left₀
    (mul_nonneg (axisWeight_pos parameters grade cell).le (norm_nonneg _)) linear 2
  rw [mul_pow, mul_pow] at squared
  exact squared

/-- The axis gradient family of a state-core field is in the accepted axis core. -/
theorem traceGradient_mem {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) :
    (fun cell => originPartial direction (field.val cell)) ∈
      Grad.AxisCore.axisCoreSubmodule parameters dimension := by
  intro grade
  have rowSummable : Summable (fun cell : ℤ =>
      ‖cellGradeRowLinear (grade := grade + 3) parameters cell (field.val cell)‖ ^ 2) := by
    have memberRow := row_norm_memlp field (grade + 3)
    have squares := (memlp_iff_summable_sq (fun cell =>
      ‖cellGradeRowLinear (grade := grade + 3) parameters cell (field.val cell)‖)).mp
      memberRow
    apply squares.congr
    intro cell
    rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply Summable.of_nonneg_of_le (fun cell => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun cell => ?_)
    (rowSummable.mul_left ((6 * Grad.CartesianState.diskSupConstant) ^ 2))
  have linear := trace_gradient_row_bound (parameters := parameters) (field.val cell)
    cell grade direction
  have squared := pow_le_pow_left₀
    (mul_nonneg (axisWeight_pos parameters grade cell).le (norm_nonneg _)) linear 2
  rw [mul_pow, mul_pow] at squared
  exact squared

/-- M27's `J0`: the literal axis value trace `h ↦ h(0, ·)`, linear into the
accepted axis core. -/
def traceZero {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ]
      Grad.AxisCore.AxisSmoothCore parameters dimension where
  toFun field := ⟨fun cell => originValue (field.val cell), traceValue_mem field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    change originValue ((first.val + second.val) cell) = _
    rw [Pi.add_apply, originValue_add]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    change originValue ((scalar • field.val) cell) = _
    rw [Pi.smul_apply, originValue_smul]
    rfl

theorem traceZero_val {dimension : ℕ} (field : ACore parameters dimension) (cell : ℤ) :
    (traceZero field).val cell = originValue (field.val cell) := rfl

/-- M27's `J_i`: the literal axis first-derivative trace `h ↦ ∂_i h(0, ·)`,
linear into the accepted axis core. -/
def traceFirst {dimension : ℕ} (direction : Fin 2) :
    ACore parameters dimension →ₗ[ℂ]
      Grad.AxisCore.AxisSmoothCore parameters dimension where
  toFun field := ⟨fun cell => originPartial direction (field.val cell),
    traceGradient_mem direction field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    change originPartial direction ((first.val + second.val) cell) = _
    rw [Pi.add_apply, originPartial_add]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    change originPartial direction ((scalar • field.val) cell) = _
    rw [Pi.smul_apply, originPartial_smul]
    rfl

theorem traceFirst_val {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) (cell : ℤ) :
    (traceFirst direction field).val cell = originPartial direction (field.val cell) := rfl

/-! ### The M27 boundedness: `J0 : A^q → T^{q-1}` and `J_i : A^q → T^{q-2}` -/

/-- The sharp `J0` bound `‖J0 h‖_{T^q} ≤ 6 C_D ‖h‖_{A^{q+1}}`, the literal
`J0 : A^s → T^{s-1}` boundedness for `s = q + 1 ≥ 2`. -/
theorem traceZero_bound {dimension : ℕ} (field : ACore parameters dimension)
    (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖Grad.AxisCore.axisEta parameters dimension grade (traceZero field)‖ ≤
      6 * Grad.CartesianState.diskSupConstant * originalGradeNorm (grade + 1) field := by
  apply axisEta_le_of_row (traceZero field) grade
    (6 * Grad.CartesianState.diskSupConstant)
    (mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le)
    field (grade + 1)
  intro cell
  exact sharp_cell_value_trace parameters (field.val cell) cell grade gradePositive

/-- The sharp `J_i` bound `‖J_i h‖_{T^q} ≤ 6 C_D ‖h‖_{A^{q+2}}`, the literal
`J_i : A^s → T^{s-2}` boundedness for `s = q + 2 ≥ 3`. -/
theorem traceFirst_bound {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖Grad.AxisCore.axisEta parameters dimension grade (traceFirst direction field)‖ ≤
      6 * Grad.CartesianState.diskSupConstant * originalGradeNorm (grade + 2) field := by
  apply axisEta_le_of_row (traceFirst direction field) grade
    (6 * Grad.CartesianState.diskSupConstant)
    (mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le)
    field (grade + 2)
  intro cell
  exact sharp_cell_gradient_trace parameters (field.val cell) cell grade gradePositive
    direction

/-- The literal-exponent form of the `J0` bound: for `2 ≤ q`,
`J0 : A^q → T^{q-1}` is bounded. -/
theorem traceZero_contract {dimension : ℕ} (field : ACore parameters dimension)
    (grade : ℕ) (gradeLarge : 2 ≤ grade) :
    ‖Grad.AxisCore.axisEta parameters dimension (grade - 1) (traceZero field)‖ ≤
      6 * Grad.CartesianState.diskSupConstant * originalGradeNorm grade field := by
  have shifted := traceZero_bound field (grade - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ grade)] at shifted

/-- The literal-exponent form of the `J_i` bound: for `3 ≤ q`,
`J_i : A^q → T^{q-2}` is bounded. -/
theorem traceFirst_contract {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) (grade : ℕ) (gradeLarge : 3 ≤ grade) :
    ‖Grad.AxisCore.axisEta parameters dimension (grade - 2)
        (traceFirst direction field)‖ ≤
      6 * Grad.CartesianState.diskSupConstant * originalGradeNorm grade field := by
  have shifted := traceFirst_bound direction field (grade - 2) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 2 ≤ grade)] at shifted

/-! ### Grade-norm triangle laws for the projection algebra -/

theorem originalGradeNorm_sub_le {dimension : ℕ} (grade : ℕ)
    (first second : ACore parameters dimension) :
    originalGradeNorm grade (first - second) ≤
      originalGradeNorm grade first + originalGradeNorm grade second := by
  unfold originalGradeNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem originalGradeNorm_add_le {dimension : ℕ} (grade : ℕ)
    (first second : ACore parameters dimension) :
    originalGradeNorm grade (first + second) ≤
      originalGradeNorm grade first + originalGradeNorm grade second := by
  unfold originalGradeNorm
  rw [map_add]
  exact norm_add_le _ _

end Grad.AxisJet
