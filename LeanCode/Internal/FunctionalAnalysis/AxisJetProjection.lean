import AxisJetTraceLaws

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### M32: the ordered formula `Q_A = I - E_A J_A` -/

/-- M32's correction `E_A J_A = E0 J0 + E1 J1 + E2 J2`. -/
def jetCorrection {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  insertZero ∘ₗ traceZero + (insertOne 0) ∘ₗ (traceFirst 0) +
    (insertOne 1) ∘ₗ (traceFirst 1)

/-- M32's ordered projection formula `Q_A = I - E_A J_A`. -/
def axisJetProjection {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  LinearMap.id - jetCorrection

theorem jetCorrection_apply {dimension : ℕ} (field : ACore parameters dimension) :
    jetCorrection field =
      insertZero (traceZero field) + insertOne 0 (traceFirst 0 field) +
        insertOne 1 (traceFirst 1 field) := rfl

theorem axisJetProjection_apply {dimension : ℕ} (field : ACore parameters dimension) :
    axisJetProjection field =
      field - (insertZero (traceZero field) + insertOne 0 (traceFirst 0 field) +
        insertOne 1 (traceFirst 1 field)) := rfl

/-! ### The trace laws of the correction and the projection kernel -/

theorem traceZero_correction {dimension : ℕ} (field : ACore parameters dimension) :
    traceZero (jetCorrection field) = traceZero field := by
  rw [jetCorrection_apply, map_add, map_add, traceZero_insertZero,
    traceZero_insertOne, traceZero_insertOne, add_zero, add_zero]

theorem traceFirst_correction {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) :
    traceFirst direction (jetCorrection field) = traceFirst direction field := by
  rw [jetCorrection_apply, map_add, map_add, traceFirst_insertZero,
    traceFirst_insertOne, traceFirst_insertOne, zero_add]
  fin_cases direction
  · rw [show ((⟨0, by omega⟩ : Fin 2) = (0 : Fin 2)) from rfl]
    rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), add_zero]
  · rw [show ((⟨1, by omega⟩ : Fin 2) = (1 : Fin 2)) from rfl]
    rw [if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, zero_add]

/-- The COR18 gate, value half: `Q_A` output has zero axis value trace. -/
theorem traceZero_projection {dimension : ℕ} (field : ACore parameters dimension) :
    traceZero (axisJetProjection field) = 0 := by
  rw [axisJetProjection_apply, ← jetCorrection_apply, map_sub,
    traceZero_correction, sub_self]

/-- The COR18 gate, jet half: `Q_A` output has zero axis first-jet trace. -/
theorem traceFirst_projection {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) :
    traceFirst direction (axisJetProjection field) = 0 := by
  rw [axisJetProjection_apply, ← jetCorrection_apply, map_sub,
    traceFirst_correction, sub_self]

/-- Cell-by-cell: `Q_A` output vanishes at the axis. -/
theorem projection_originValue {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) :
    originValue ((axisJetProjection field).val cell) = 0 :=
  congrFun (congrArg Subtype.val (traceZero_projection field)) cell

/-- Cell-by-cell: `Q_A` output has zero first Cartesian jet at the axis. -/
theorem projection_originPartial {dimension : ℕ} (field : ACore parameters dimension)
    (direction : Fin 2) (cell : ℤ) :
    originPartial direction ((axisJetProjection field).val cell) = 0 :=
  congrFun (congrArg Subtype.val (traceFirst_projection direction field)) cell

/-! ### Fixed points, idempotence and the exact range -/

/-- Fields already flat at the axis are fixed by `Q_A`. -/
theorem projection_fixes {dimension : ℕ} (field : ACore parameters dimension)
    (valueFlat : ∀ cell : ℤ, originValue (field.val cell) = 0)
    (gradientFlat : ∀ (direction : Fin 2) (cell : ℤ),
      originPartial direction (field.val cell) = 0) :
    axisJetProjection field = field := by
  have zeroTraceZero : traceZero (parameters := parameters) field = 0 := by
    apply Subtype.ext
    funext cell
    show originValue (field.val cell) = _
    rw [valueFlat cell]
    rfl
  have zeroTraceFirst : ∀ direction : Fin 2,
      traceFirst (parameters := parameters) direction field = 0 := by
    intro direction
    apply Subtype.ext
    funext cell
    show originPartial direction (field.val cell) = _
    rw [gradientFlat direction cell]
    rfl
  rw [axisJetProjection_apply, zeroTraceZero, zeroTraceFirst 0, zeroTraceFirst 1,
    map_zero, map_zero, map_zero, add_zero, add_zero, sub_zero]

/-- M32: `Q_A` is idempotent. -/
theorem projection_idempotent {dimension : ℕ} (field : ACore parameters dimension) :
    axisJetProjection (axisJetProjection field) = axisJetProjection field := by
  apply projection_fixes
  · intro cell
    exact projection_originValue field cell
  · intro direction cell
    exact projection_originPartial field direction cell

/-- M32: the range of `Q_A` is exactly the flat fields — zero value and
zero first Cartesian jet at the axis. -/
theorem mem_range_projection_iff {dimension : ℕ} (field : ACore parameters dimension) :
    (∃ source : ACore parameters dimension, axisJetProjection source = field) ↔
      ((∀ cell : ℤ, originValue (field.val cell) = 0) ∧
        ∀ (direction : Fin 2) (cell : ℤ),
          originPartial direction (field.val cell) = 0) := by
  constructor
  · rintro ⟨source, sourceEq⟩
    constructor
    · intro cell
      rw [← sourceEq]
      exact projection_originValue source cell
    · intro direction cell
      rw [← sourceEq]
      exact projection_originPartial source direction cell
  · rintro ⟨valueFlat, gradientFlat⟩
    exact ⟨field, projection_fixes field valueFlat gradientFlat⟩

/-- `Q_A` annihilates every inserted profile: `Q_A E_A = 0` on the value
component. -/
theorem projection_insertZero {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    axisJetProjection (insertZero family) = 0 := by
  rw [axisJetProjection_apply, traceZero_insertZero, traceFirst_insertZero,
    traceFirst_insertZero, map_zero, map_zero, add_zero, add_zero, sub_self]

/-! ### M32: the same-grade bound for `q ≥ 3` -/

/-- M32's same-grade bound in shift form: one constant per grade
`q = shift + 3`, uniform over the state core. -/
theorem projection_bound {dimension : ℕ} (shift : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ field : ACore parameters dimension,
      originalGradeNorm (shift + 3) (axisJetProjection field) ≤
        bound * originalGradeNorm (shift + 3) field := by
  obtain ⟨zeroBound, zeroNonneg, zeroLe⟩ :=
    insertZero_bound (parameters := parameters) (dimension := dimension) (shift + 2)
  obtain ⟨oneBoundLeft, oneNonnegLeft, oneLeLeft⟩ :=
    insertOne_bound (parameters := parameters) (dimension := dimension) 0 (shift + 1)
  obtain ⟨oneBoundRight, oneNonnegRight, oneLeRight⟩ :=
    insertOne_bound (parameters := parameters) (dimension := dimension) 1 (shift + 1)
  have supNonneg : (0 : ℝ) ≤ 6 * Grad.CartesianState.diskSupConstant :=
    mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le
  refine ⟨1 + zeroBound * (6 * Grad.CartesianState.diskSupConstant) +
    oneBoundLeft * (6 * Grad.CartesianState.diskSupConstant) +
    oneBoundRight * (6 * Grad.CartesianState.diskSupConstant), ?_, ?_⟩
  · exact add_nonneg (add_nonneg (add_nonneg zero_le_one
      (mul_nonneg zeroNonneg supNonneg)) (mul_nonneg oneNonnegLeft supNonneg))
      (mul_nonneg oneNonnegRight supNonneg)
  intro field
  have insertZeroPart : originalGradeNorm (shift + 3)
      (insertZero (traceZero field)) ≤
      zeroBound * (6 * Grad.CartesianState.diskSupConstant) *
        originalGradeNorm (shift + 3) field := by
    have step := zeroLe (traceZero field)
    rw [show shift + 2 + 1 = shift + 3 from rfl] at step
    apply step.trans
    have traceStep := traceZero_bound field (shift + 2) (by omega)
    rw [show shift + 2 + 1 = shift + 3 from rfl] at traceStep
    apply le_trans (mul_le_mul_of_nonneg_left traceStep zeroNonneg)
    apply le_of_eq
    ring
  have insertOnePartLeft : originalGradeNorm (shift + 3)
      (insertOne 0 (traceFirst 0 field)) ≤
      oneBoundLeft * (6 * Grad.CartesianState.diskSupConstant) *
        originalGradeNorm (shift + 3) field := by
    have step := oneLeLeft (traceFirst 0 field)
    rw [show shift + 1 + 2 = shift + 3 from rfl] at step
    apply step.trans
    have traceStep := traceFirst_bound 0 field (shift + 1) (by omega)
    rw [show shift + 1 + 2 = shift + 3 from rfl] at traceStep
    apply le_trans (mul_le_mul_of_nonneg_left traceStep oneNonnegLeft)
    apply le_of_eq
    ring
  have insertOnePartRight : originalGradeNorm (shift + 3)
      (insertOne 1 (traceFirst 1 field)) ≤
      oneBoundRight * (6 * Grad.CartesianState.diskSupConstant) *
        originalGradeNorm (shift + 3) field := by
    have step := oneLeRight (traceFirst 1 field)
    rw [show shift + 1 + 2 = shift + 3 from rfl] at step
    apply step.trans
    have traceStep := traceFirst_bound 1 field (shift + 1) (by omega)
    rw [show shift + 1 + 2 = shift + 3 from rfl] at traceStep
    apply le_trans (mul_le_mul_of_nonneg_left traceStep oneNonnegRight)
    apply le_of_eq
    ring
  set correction : ACore parameters dimension := insertZero (traceZero field) +
    insertOne 0 (traceFirst 0 field) + insertOne 1 (traceFirst 1 field)
    with correctionDef
  rw [axisJetProjection_apply, ← correctionDef]
  apply (originalGradeNorm_sub_le (shift + 3) field correction).trans
  have sumSplit : originalGradeNorm (shift + 3) correction ≤
      originalGradeNorm (shift + 3) (insertZero (traceZero field)) +
        originalGradeNorm (shift + 3) (insertOne 0 (traceFirst 0 field)) +
        originalGradeNorm (shift + 3) (insertOne 1 (traceFirst 1 field)) := by
    rw [correctionDef]
    apply le_trans (originalGradeNorm_add_le _ _ _)
    apply add_le_add (originalGradeNorm_add_le _ _ _) le_rfl
  apply le_trans (add_le_add le_rfl sumSplit)
  apply le_trans (add_le_add le_rfl (add_le_add
    (add_le_add insertZeroPart insertOnePartLeft) insertOnePartRight))
  apply le_of_eq
  ring

/-- M32's same-grade bound in the literal exponent form: for every
`3 ≤ q`, `‖Q_A h‖_{A^q} ≤ C_q ‖h‖_{A^q}`. -/
theorem projection_bound_contract {dimension : ℕ} (grade : ℕ)
    (gradeLarge : 3 ≤ grade) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ field : ACore parameters dimension,
      originalGradeNorm grade (axisJetProjection field) ≤
        bound * originalGradeNorm grade field := by
  obtain ⟨bound, boundNonneg, boundLe⟩ :=
    projection_bound (parameters := parameters) (dimension := dimension) (grade - 3)
  refine ⟨bound, boundNonneg, ?_⟩
  intro field
  have shifted := boundLe field
  rwa [Nat.sub_add_cancel gradeLarge] at shifted

end Grad.AxisJet
