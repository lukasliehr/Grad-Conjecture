import AKCR1OriginalSmoothStateLimit
import NewtonExactZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped Topology

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.NashMoser.Numeric

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (low : AdmissibleGrade)

/-- Each grade sees the original core of the same guarded Newton state. -/
def originalNewtonGradeMap (grade : AdmissibleGrade) :
    StateGradeCore parameters reference inside low.val low.property →+
      stateRange parameters reference inside grade.val grade.property :=
  ((stateSmoothEmbedding parameters reference inside grade.val grade.property).comp
    NormedCoreCopy.toCoreLinear).toAddMonoidHom

variable {F : Type*} [NormedAddCommGroup F]
    {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
    (data : GuardedNewtonData (StateGradeCore parameters reference inside low.val low.property)
      F initial radius highConstant quadratic smoothing loss)
    (gradeConstant : AdmissibleGrade → ℝ)
    (nonnegative : ∀ grade, 0 ≤ gradeConstant grade)
    (gradeBound : ∀ grade index,
      ‖data.gradeCorrection (originalNewtonGradeMap parameters reference inside low grade) index‖ ≤
        gradeConstant grade * newtonTime initial index ^ ((grade.val : ℝ) + loss) *
          ‖data.mapping (data.iterate index)‖)

include gradeConstant nonnegative gradeBound in
theorem originalNewtonConverges (grade : AdmissibleGrade) :
    ∃ limit : stateRange parameters reference inside grade.val grade.property,
      Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
        (data.iterate index).toCore) atTop (𝓝 limit) := by
  refine ⟨data.gradeLimit (originalNewtonGradeMap parameters reference inside low grade), ?_⟩
  exact data.grade_iterate_tendsto (originalNewtonGradeMap parameters reference inside low grade)
    ((grade.val : ℝ) + loss) (gradeConstant grade) (nonnegative grade) (gradeBound grade)

/-- The guarded iteration now yields one actual smooth constrained core,
not only a collection of completed-grade limits. The quantitative inputs
remain the stated Newton hypotheses until the PDE inverse is instantiated. -/
def originalNewtonLimit : stateSmoothRange parameters reference inside :=
  convergentStateLimit parameters reference inside (fun index => (data.iterate index).toCore)
    (originalNewtonConverges parameters reference inside low data gradeConstant nonnegative gradeBound)

theorem originalNewtonLimit_tendsto (grade : AdmissibleGrade) :
    Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
      (data.iterate index).toCore) atTop
      (𝓝 (stateSmoothEmbedding parameters reference inside grade.val grade.property
        (originalNewtonLimit parameters reference inside low data gradeConstant nonnegative gradeBound))) :=
  convergentStateLimit_tendsto parameters reference inside _ _ grade

theorem originalNewtonLimit_low_norm :
    ‖stateSmoothEmbedding parameters reference inside low.val low.property
      (originalNewtonLimit parameters reference inside low data gradeConstant nonnegative gradeBound)‖ ≤ radius / 2 := by
  apply convergentStateLimit_norm_le parameters reference inside _ _ low
  intro index
  exact data.iterate_norm_le_half index

theorem originalNewtonLimit_exact_zero (grade : AdmissibleGrade)
    (completedMapping : stateRange parameters reference inside grade.val grade.property → F)
    (realization : ∀ state, completedMapping
      (originalNewtonGradeMap parameters reference inside low grade state) = data.mapping state)
    (continuous : ContinuousAt completedMapping
      (stateSmoothEmbedding parameters reference inside grade.val grade.property
        (originalNewtonLimit parameters reference inside low data gradeConstant nonnegative gradeBound))) :
    data.mapping ⟨originalNewtonLimit parameters reference inside low data gradeConstant nonnegative gradeBound⟩ = 0 := by
  exact data.exact_zero_of_grade_limit (originalNewtonGradeMap parameters reference inside low grade)
    ⟨originalNewtonLimit parameters reference inside low data gradeConstant nonnegative gradeBound⟩
    completedMapping realization continuous
    (originalNewtonLimit_tendsto parameters reference inside low data gradeConstant nonnegative gradeBound grade)

end Grad.NashMoser.OriginalLimit
