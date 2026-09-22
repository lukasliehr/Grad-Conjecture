import BT19CoreMap
import FC10Extension

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

/-- The unique bounded extension of the actual trace to the original A^q completion. -/
def completedTrace {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    AGrade parameters dimension grade →L[ℂ] BoundaryGrade parameters (ComplexEuclidean dimension) grade :=
  denseCoreExtension parameters (coreTraceLinear parameters grade gradePositive)
    (Real.sqrt (traceCellConstant grade)) (coreTraceLinear_norm_le parameters grade gradePositive)

theorem completedTrace_apply_eta {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : GradeCore parameters dimension grade) :
    completedTrace parameters grade gradePositive (aGradeEta parameters field) =
      coreTraceLinear parameters grade gradePositive field :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem completedTrace_coefficient {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : GradeCore parameters dimension grade) (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade
      (completedTrace parameters grade gradePositive (aGradeEta parameters field)) mode =
      originalBoundaryCoefficient parameters field.toCore mode := by
  rw [completedTrace_apply_eta, coreTraceLinear_coefficient]

theorem completedTrace_norm_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    ‖completedTrace (dimension := dimension) parameters grade gradePositive‖ ≤
      Real.sqrt (traceCellConstant grade) :=
  denseCoreExtension_norm_le parameters _ _ (Real.sqrt_nonneg _) _

theorem completedTrace_apply_norm_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : AGrade parameters dimension grade) :
    ‖completedTrace parameters grade gradePositive field‖ ≤
      Real.sqrt (traceCellConstant grade) * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

theorem completedTrace_apply_norm_sq_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : AGrade parameters dimension grade) :
    ‖completedTrace parameters grade gradePositive field‖ ^ 2 ≤
      traceCellConstant grade * ‖field‖ ^ 2 := by
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (completedTrace_apply_norm_le parameters grade gradePositive field) 2
  simpa only [mul_pow, Real.sq_sqrt (traceCellConstant_nonnegative grade)] using bound

theorem completedTrace_weighted_bound {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : AGrade parameters dimension grade) :
    (∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      boundaryFrequency mode ^ (2 * grade - 1) *
      ‖boundaryCoefficient parameters grade (completedTrace parameters grade gradePositive field) mode‖ ^ 2) ≤
      traceCellConstant grade * ‖field‖ ^ 2 := by
  rw [← boundary_norm_sq]
  exact completedTrace_apply_norm_sq_le parameters grade gradePositive field

theorem completedTrace_unique {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade)
    (other : AGrade parameters dimension grade →L[ℂ] BoundaryGrade parameters (ComplexEuclidean dimension) grade)
    (coreLaw : ∀ field : GradeCore parameters dimension grade, ∀ mode : ℤ × ℤ,
      boundaryCoefficient parameters grade (other (aGradeEta parameters field)) mode =
        originalBoundaryCoefficient parameters field.toCore mode) :
    other = completedTrace parameters grade gradePositive := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  apply Subtype.ext
  funext mode
  change other (aGradeEta parameters field) mode =
    completedTrace parameters grade gradePositive (aGradeEta parameters field) mode
  rw [← boundary_weighted_coefficient parameters grade (other (aGradeEta parameters field)) mode,
    ← boundary_weighted_coefficient parameters grade
      (completedTrace parameters grade gradePositive (aGradeEta parameters field)) mode,
    coreLaw, completedTrace_coefficient]

end Grad.BoundaryTrace
