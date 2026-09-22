import GC21Completion

noncomputable section

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

def apHighCoordinates {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) :=
  if 3 ≤ |mode.1| then field mode else 0

theorem apHighCoordinates_norm_le {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) :
    ‖apHighCoordinates L sigma gamma ell grade field mode‖ ≤ ‖field mode‖ := by
  unfold apHighCoordinates
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (field mode)

def apHighLinear {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell dimension grade →ₗ[ℂ] APBoundaryGrade L sigma gamma ell dimension grade where
  toFun field := ⟨apHighCoordinates L sigma gamma ell grade field,
    field.property.mono' (apHighCoordinates_norm_le L sigma gamma ell grade field)⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change (if 3 ≤ |mode.1| then first mode + second mode else 0) =
      (if 3 ≤ |mode.1| then first mode else 0) + (if 3 ≤ |mode.1| then second mode else 0)
    split_ifs <;> simp
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change (if 3 ≤ |mode.1| then scalar • field mode else 0) =
      scalar • (if 3 ≤ |mode.1| then field mode else 0)
    split_ifs <;> simp

def apHighProjection {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell dimension grade →L[ℂ] APBoundaryGrade L sigma gamma ell dimension grade :=
  (apHighLinear L sigma gamma ell grade).mkContinuous 1 (fun field => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (apHighCoordinates_norm_le L sigma gamma ell grade field))

theorem apHighProjection_apply {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) :
    apHighProjection L sigma gamma ell grade field mode = if 3 ≤ |mode.1| then field mode else 0 := rfl

theorem apHighProjection_bound {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) :
    ‖apHighProjection L sigma gamma ell grade field‖ ≤ ‖field‖ :=
  lp.norm_mono (by norm_num) (apHighCoordinates_norm_le L sigma gamma ell grade field)

theorem apHighProjection_idempotent {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) :
    apHighProjection L sigma gamma ell grade (apHighProjection L sigma gamma ell grade field) =
      apHighProjection L sigma gamma ell grade field := by
  apply Subtype.ext
  funext mode
  simp only [apHighProjection_apply]
  split_ifs <;> rfl

theorem apHighProjection_coefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade (apHighProjection L sigma gamma ell grade field) mode =
      if 3 ≤ |mode.1| then apBoundaryCoefficient L sigma gamma ell grade field mode else 0 := by
  simp only [apBoundaryCoefficient, apHighProjection_apply]
  split_ifs <;> simp

def apHighTrace {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] APBoundaryGrade L sigma gamma ell dimension grade :=
  (apHighProjection L sigma gamma ell grade).comp (apBoundaryTrace L sigma gamma ell grade gradePositive)

theorem apHighTrace_bound {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : apGrade L sigma gamma ell dimension grade) :
    ‖apHighTrace L sigma gamma ell grade gradePositive field‖ ≤ Real.sqrt (traceCellConstant grade) * ‖field‖ :=
  (apHighProjection_bound L sigma gamma ell grade _).trans
    (apBoundaryTrace_bound L sigma gamma ell grade gradePositive field)

end Grad.GaugeCoefficients.Physical.WeightedTrace
