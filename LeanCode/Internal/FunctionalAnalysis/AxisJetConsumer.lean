import AxisJetProjection

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### The immediate exact consumer of the A25-A29 block

Everything below is consumed at the vector component of the accepted state
carrier, `ACore parameters 3`, which is the `Q_A` domain of the COR18 N8
composition. -/

/-- N8's gate, consumed: `Q_A` output has zero value and zero first
Cartesian jet at the axis, and `Q_A` is idempotent. -/
theorem consumed_projection_gate (field : ACore parameters 3) :
    (∀ cell : ℤ, originValue ((axisJetProjection field).val cell) = 0) ∧
    (∀ (direction : Fin 2) (cell : ℤ),
      originPartial direction ((axisJetProjection field).val cell) = 0) ∧
    axisJetProjection (axisJetProjection field) = axisJetProjection field := by
  refine ⟨?_, ?_, projection_idempotent field⟩
  · intro cell
    exact projection_originValue field cell
  · intro direction cell
    exact projection_originPartial field direction cell

/-- N8's gate, consumed: fields already satisfying the flatness are fixed
by `Q_A`. -/
theorem consumed_projection_fixes (field : ACore parameters 3)
    (valueFlat : ∀ cell : ℤ, originValue (field.val cell) = 0)
    (gradientFlat : ∀ (direction : Fin 2) (cell : ℤ),
      originPartial direction (field.val cell) = 0) :
    axisJetProjection field = field :=
  projection_fixes field valueFlat gradientFlat

/-- Consumed range law: the range of `Q_A` on the vector component is
exactly the zero-value, zero-first-jet fields. -/
theorem consumed_projection_range (field : ACore parameters 3) :
    (∃ source : ACore parameters 3, axisJetProjection source = field) ↔
      ((∀ cell : ℤ, originValue (field.val cell) = 0) ∧
        ∀ (direction : Fin 2) (cell : ℤ),
          originPartial direction (field.val cell) = 0) :=
  mem_range_projection_iff field

/-- Consumed M32 bound: for every `3 ≤ q` the projection is bounded on the
grade-`q` original norm of the vector component, with one constant per
grade. -/
theorem consumed_projection_bound (grade : ℕ) (gradeLarge : 3 ≤ grade) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ field : ACore parameters 3,
      originalGradeNorm grade (axisJetProjection field) ≤
        bound * originalGradeNorm grade field :=
  projection_bound_contract grade gradeLarge

/-- Consumed M31 matrix at the vector component: the four literal trace
laws of the profiles. -/
theorem consumed_trace_matrix (family : Grad.AxisCore.AxisSmoothCore parameters 3) :
    traceZero (insertZero family) = family ∧
    (∀ direction : Fin 2, traceFirst direction (insertZero family) = 0) ∧
    (∀ coordinate : Fin 2, traceZero (insertOne coordinate family) = 0) ∧
    ∀ direction coordinate : Fin 2,
      traceFirst direction (insertOne coordinate family) =
        if direction = coordinate then family else 0 := by
  refine ⟨traceZero_insertZero family, ?_, ?_, ?_⟩
  · intro direction
    exact traceFirst_insertZero direction family
  · intro coordinate
    exact traceZero_insertOne coordinate family
  · intro direction coordinate
    exact traceFirst_insertOne direction coordinate family

/-- `Q_A` annihilates the value-profile insertions of the vector component. -/
theorem consumed_projection_insertZero
    (family : Grad.AxisCore.AxisSmoothCore parameters 3) :
    axisJetProjection (insertZero family) = 0 :=
  projection_insertZero family

/-- `Q_A` annihilates the coordinate-profile insertions of the vector
component, exercising all four M31 laws. -/
theorem consumed_projection_insertOne (coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters 3) :
    axisJetProjection (insertOne coordinate family) = 0 := by
  rw [axisJetProjection_apply, traceZero_insertOne, map_zero,
    traceFirst_insertOne, traceFirst_insertOne]
  fin_cases coordinate
  · rw [show ((⟨0, by omega⟩ : Fin 2) = (0 : Fin 2)) from rfl]
    rw [if_pos rfl, if_neg (by decide : ¬(1 : Fin 2) = 0), map_zero, zero_add,
      add_zero, sub_self]
  · rw [show ((⟨1, by omega⟩ : Fin 2) = (1 : Fin 2)) from rfl]
    rw [if_neg (by decide : ¬(0 : Fin 2) = 1), if_pos rfl, map_zero, zero_add,
      zero_add, sub_self]

/-- Consumed M30 bounds at the vector component, in the literal grade
shifts of the card. -/
theorem consumed_profile_bounds (grade : ℕ) :
    (∃ bound : ℝ, 0 ≤ bound ∧
      ∀ family : Grad.AxisCore.AxisSmoothCore parameters 3,
      originalGradeNorm (grade + 1) (insertZero family) ≤
        bound * ‖Grad.AxisCore.axisEta parameters 3 grade family‖) ∧
    ∀ coordinate : Fin 2, ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ family : Grad.AxisCore.AxisSmoothCore parameters 3,
      originalGradeNorm (grade + 2) (insertOne coordinate family) ≤
        bound * ‖Grad.AxisCore.axisEta parameters 3 grade family‖ := by
  refine ⟨insertZero_bound grade, ?_⟩
  intro coordinate
  exact insertOne_bound coordinate grade

/-- Consumed M27 bounds at the vector component, in the literal grade
shifts of the card. -/
theorem consumed_trace_bounds (field : ACore parameters 3) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    ‖Grad.AxisCore.axisEta parameters 3 grade (traceZero field)‖ ≤
      6 * Grad.CartesianState.diskSupConstant *
        originalGradeNorm (grade + 1) field ∧
    ∀ direction : Fin 2,
      ‖Grad.AxisCore.axisEta parameters 3 grade (traceFirst direction field)‖ ≤
        6 * Grad.CartesianState.diskSupConstant *
          originalGradeNorm (grade + 2) field := by
  refine ⟨traceZero_bound field grade gradePositive, ?_⟩
  intro direction
  exact traceFirst_bound direction field grade gradePositive

end Grad.AxisJet
