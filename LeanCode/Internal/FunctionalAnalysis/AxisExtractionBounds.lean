import AxisSharpGradient

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Grade norms as sequence norms -/

theorem originalGradeNorm_eq_lp {dimension : ℕ} (field : ACore parameters dimension)
    (grade : ℕ) :
    originalGradeNorm grade field =
      ‖(⟨rawCartesianGradeCoordinates parameters grade field.val, field.property grade⟩ :
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2)‖ := by
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply]
  rfl

/-- The norm sequence of a square-summable sequence has the same norm. -/
theorem lp_norm_of_norms {E : ℤ → Type*} [∀ cell, NormedAddCommGroup (E cell)]
    (element : lp E 2) :
    ‖(⟨fun cell => ‖element.val cell‖, element.property.norm⟩ :
      lp (fun _ : ℤ => ℝ) 2)‖ = ‖element‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro cell
    exact (Real.norm_of_nonneg (norm_nonneg _)).le
  · apply lp.norm_mono (by norm_num)
    intro cell
    exact (Real.norm_of_nonneg (norm_nonneg _)).ge

/-- The two-row summation: a coordinatewise bound of the weighted axis
coordinates by two grade rows sums to the corresponding norm bound. -/
theorem axisGradeNorm_le_of_two_rows {firstDimension secondDimension : ℕ}
    (sequence : TCore parameters) (grade : ℕ) (bound : ℝ) (boundNonneg : 0 ≤ bound)
    (first : ACore parameters firstDimension) (second : ACore parameters secondDimension)
    (rowGrade : ℕ)
    (dominated : ∀ cell : ℤ, axisWeight parameters grade cell * ‖sequence.val cell‖ ≤
      bound * (‖cellGradeRowLinear (grade := rowGrade) parameters cell (first.val cell)‖ +
        ‖cellGradeRowLinear (grade := rowGrade) parameters cell (second.val cell)‖)) :
    axisGradeNorm parameters grade sequence ≤
      bound * (originalGradeNorm rowGrade first + originalGradeNorm rowGrade second) := by
  set firstNorms : lp (fun _ : ℤ => ℝ) 2 :=
    ⟨fun cell => ‖rawCartesianGradeCoordinates parameters rowGrade first.val cell‖,
      (first.property rowGrade).norm⟩ with firstNormsDef
  set secondNorms : lp (fun _ : ℤ => ℝ) 2 :=
    ⟨fun cell => ‖rawCartesianGradeCoordinates parameters rowGrade second.val cell‖,
      (second.property rowGrade).norm⟩ with secondNormsDef
  have firstEq : ‖firstNorms‖ = originalGradeNorm rowGrade first := by
    rw [originalGradeNorm_eq_lp first rowGrade, firstNormsDef]
    exact lp_norm_of_norms
      (⟨rawCartesianGradeCoordinates parameters rowGrade first.val,
        first.property rowGrade⟩ : lp (fun _ : ℤ => CartesianGradeRow firstDimension
          rowGrade) 2)
  have secondEq : ‖secondNorms‖ = originalGradeNorm rowGrade second := by
    rw [originalGradeNorm_eq_lp second rowGrade, secondNormsDef]
    exact lp_norm_of_norms
      (⟨rawCartesianGradeCoordinates parameters rowGrade second.val,
        second.property rowGrade⟩ : lp (fun _ : ℤ => CartesianGradeRow secondDimension
          rowGrade) 2)
  have majorantNorm : ‖(bound : ℝ) • (firstNorms + secondNorms)‖ ≤
      bound * (originalGradeNorm rowGrade first + originalGradeNorm rowGrade second) := by
    rw [norm_smul, Real.norm_of_nonneg boundNonneg]
    apply mul_le_mul_of_nonneg_left _ boundNonneg
    apply (norm_add_le _ _).trans
    rw [firstEq, secondEq]
  apply le_trans _ majorantNorm
  unfold axisGradeNorm
  apply lp.norm_mono (by norm_num)
  intro cell
  have coordinateNorm : ‖axisCoordinates parameters grade sequence.val cell‖ =
      axisWeight parameters grade cell * ‖sequence.val cell‖ := by
    unfold axisCoordinates
    rw [norm_smul, Real.norm_of_nonneg (axisWeight_pos parameters grade cell).le]
  change ‖axisCoordinates parameters grade sequence.val cell‖ ≤ _
  rw [coordinateNorm]
  apply (dominated cell).trans
  have valueForm : ((bound : ℝ) • (firstNorms + secondNorms)).val cell =
      bound * (‖rawCartesianGradeCoordinates parameters rowGrade first.val cell‖ +
        ‖rawCartesianGradeCoordinates parameters rowGrade second.val cell‖) := rfl
  have rowForm : bound *
      (‖cellGradeRowLinear (grade := rowGrade) parameters cell (first.val cell)‖ +
        ‖cellGradeRowLinear (grade := rowGrade) parameters cell (second.val cell)‖) =
      ((bound : ℝ) • (firstNorms + secondNorms)).val cell := by
    rw [valueForm, raw_norm_eq_row, raw_norm_eq_row]
  rw [rowForm]
  exact le_abs_self _

/-! ### AL14 at the coefficient-core level -/

/-- The direction-extraction constant. -/
def kappaTraceConstant : ℝ := 12 * Grad.CartesianState.diskSupConstant

theorem kappaTraceConstant_nonneg : 0 ≤ kappaTraceConstant :=
  mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le

/-- The scalar gradient trace at any grade, against the two-shifted row. -/
theorem scalarGradient_grade_bound (field : ACore parameters 1) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    axisGradeNorm parameters grade
        ⟨fun cell => scalarOriginGradient field cell, scalarOriginGradient_mem field⟩ ≤
      kappaTraceConstant * originalGradeNorm (grade + 2) field := by
  have summed := axisGradeNorm_le_of_two_rows
    ⟨fun cell => scalarOriginGradient field cell, scalarOriginGradient_mem field⟩
    grade (6 * Grad.CartesianState.diskSupConstant)
    (mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le)
    field field (grade + 2) ?_
  · apply summed.trans
    unfold kappaTraceConstant
    apply le_of_eq
    ring
  intro cell
  have gradientNorm : ‖scalarOriginGradient field cell‖ ≤
      ‖originPartial 0 (field.val cell)‖ + ‖originPartial 1 (field.val cell)‖ := by
    unfold scalarOriginGradient
    exact (planarPair_norm_le _ _).trans
      (add_le_add (PiLp.norm_apply_le _ 0) (PiLp.norm_apply_le _ 0))
  have firstTrace := sharp_cell_gradient_trace parameters (field.val cell) cell grade
    gradePositive 0
  have secondTrace := sharp_cell_gradient_trace parameters (field.val cell) cell grade
    gradePositive 1
  calc axisWeight parameters grade cell * ‖scalarOriginGradient field cell‖ ≤
      axisWeight parameters grade cell * (‖originPartial 0 (field.val cell)‖ +
        ‖originPartial 1 (field.val cell)‖) :=
        mul_le_mul_of_nonneg_left gradientNorm (axisWeight_pos parameters grade cell).le
    _ = axisWeight parameters grade cell * ‖originPartial 0 (field.val cell)‖ +
        axisWeight parameters grade cell * ‖originPartial 1 (field.val cell)‖ := by ring
    _ ≤ 6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ +
        6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ :=
        add_le_add firstTrace secondTrace
    _ = 6 * Grad.CartesianState.diskSupConstant *
        (‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ +
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖) := by
        ring

/-- The tangential gradient trace at any grade, against the two-shifted row. -/
theorem tangentialGradient_grade_bound (field : ACore parameters 3) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    axisGradeNorm parameters grade
        ⟨fun cell => tangentialOriginGradient field cell,
          tangentialOriginGradient_mem field⟩ ≤
      kappaTraceConstant * originalGradeNorm (grade + 2) field := by
  have summed := axisGradeNorm_le_of_two_rows
    ⟨fun cell => tangentialOriginGradient field cell, tangentialOriginGradient_mem field⟩
    grade (6 * Grad.CartesianState.diskSupConstant)
    (mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le)
    field field (grade + 2) ?_
  · apply summed.trans
    unfold kappaTraceConstant
    apply le_of_eq
    ring
  intro cell
  have gradientNorm : ‖tangentialOriginGradient field cell‖ ≤
      ‖originPartial 0 (field.val cell)‖ + ‖originPartial 1 (field.val cell)‖ := by
    unfold tangentialOriginGradient
    exact (planarPair_norm_le _ _).trans
      (add_le_add (PiLp.norm_apply_le _ 1) (PiLp.norm_apply_le _ 1))
  have firstTrace := sharp_cell_gradient_trace parameters (field.val cell) cell grade
    gradePositive 0
  have secondTrace := sharp_cell_gradient_trace parameters (field.val cell) cell grade
    gradePositive 1
  calc axisWeight parameters grade cell * ‖tangentialOriginGradient field cell‖ ≤
      axisWeight parameters grade cell * (‖originPartial 0 (field.val cell)‖ +
        ‖originPartial 1 (field.val cell)‖) :=
        mul_le_mul_of_nonneg_left gradientNorm (axisWeight_pos parameters grade cell).le
    _ = axisWeight parameters grade cell * ‖originPartial 0 (field.val cell)‖ +
        axisWeight parameters grade cell * ‖originPartial 1 (field.val cell)‖ := by ring
    _ ≤ 6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ +
        6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ :=
        add_le_add firstTrace secondTrace
    _ = 6 * Grad.CartesianState.diskSupConstant *
        (‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖ +
          ‖cellGradeRowLinear (grade := grade + 2) parameters cell (field.val cell)‖) := by
        ring

/-- AL14 at the coefficient-core level: the direction extraction costs
exactly three grades, with `T^{q+1}` data norms. -/
theorem kappaData_bound (direction : QuotientState parameters) (grade : ℕ) :
    axisDataNorm parameters grade (kappaData direction) ≤
      2 * kappaTraceConstant * stateNorm (grade + 3) direction := by
  unfold axisDataNorm kappaData
  set scalarData : TCore parameters :=
    ⟨fun cell => scalarOriginGradient (statePotential direction) cell,
      scalarOriginGradient_mem (statePotential direction)⟩ with scalarDataDef
  set tangentialData : TCore parameters :=
    ⟨fun cell => tangentialOriginGradient (stateField direction) cell,
      tangentialOriginGradient_mem (stateField direction)⟩ with tangentialDataDef
  have scalarBound := scalarGradient_grade_bound (statePotential direction) (grade + 1)
    (by omega)
  have tangentialBound := tangentialGradient_grade_bound (stateField direction) (grade + 1)
    (by omega)
  rw [← scalarDataDef] at scalarBound
  rw [← tangentialDataDef] at tangentialBound
  have potentialLe : originalGradeNorm (grade + 1 + 2) (statePotential direction) ≤
      stateNorm (grade + 3) direction := by
    have := originalGradeNorm_statePotential_le (grade + 3) direction
    have gradeEq : grade + 1 + 2 = grade + 3 := by omega
    rw [gradeEq]
    exact this
  have fieldLe : originalGradeNorm (grade + 1 + 2) (stateField direction) ≤
      stateNorm (grade + 3) direction := by
    have := originalGradeNorm_stateField_le (grade + 3) direction
    have gradeEq : grade + 1 + 2 = grade + 3 := by omega
    rw [gradeEq]
    exact this
  calc axisGradeNorm parameters (grade + 1) scalarData +
      axisGradeNorm parameters (grade + 1) tangentialData ≤
      kappaTraceConstant * originalGradeNorm (grade + 1 + 2) (statePotential direction) +
        kappaTraceConstant * originalGradeNorm (grade + 1 + 2) (stateField direction) :=
        add_le_add scalarBound tangentialBound
    _ ≤ kappaTraceConstant * stateNorm (grade + 3) direction +
        kappaTraceConstant * stateNorm (grade + 3) direction :=
        add_le_add (mul_le_mul_of_nonneg_left potentialLe kappaTraceConstant_nonneg)
          (mul_le_mul_of_nonneg_left fieldLe kappaTraceConstant_nonneg)
    _ = 2 * kappaTraceConstant * stateNorm (grade + 3) direction := by ring

end Grad.AxisSplit
