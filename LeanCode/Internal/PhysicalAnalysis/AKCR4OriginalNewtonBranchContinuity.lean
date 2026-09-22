import AKCR3UniformGuardedGradeConvergence

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
    {Parameter F : Type*} [TopologicalSpace Parameter] [Nonempty Parameter]
    [NormedAddCommGroup F]
    {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
    (data : Parameter → GuardedNewtonData (StateGradeCore parameters reference inside low.val low.property)
      F initial radius highConstant quadratic smoothing loss)
    (gradeConstant : AdmissibleGrade → ℝ)
    (nonnegative : ∀ grade, 0 ≤ gradeConstant grade)
    (gradeBound : ∀ point grade index,
      ‖(data point).gradeCorrection (originalNewtonGradeMap parameters reference inside low grade) index‖ ≤
        gradeConstant grade * newtonTime initial index ^ ((grade.val : ℝ) + loss) *
          ‖(data point).mapping ((data point).iterate index)‖)

omit [TopologicalSpace Parameter] [Nonempty Parameter] in
theorem originalNewtonBranch_grade_limit (point : Parameter) (grade : AdmissibleGrade) :
    stateSmoothEmbedding parameters reference inside grade.val grade.property
      (originalNewtonLimit parameters reference inside low (data point) gradeConstant nonnegative (gradeBound point)) =
      (data point).gradeLimit (originalNewtonGradeMap parameters reference inside low grade) := by
  apply tendsto_nhds_unique
    (originalNewtonLimit_tendsto parameters reference inside low (data point) gradeConstant nonnegative (gradeBound point) grade)
  exact (data point).grade_iterate_tendsto (originalNewtonGradeMap parameters reference inside low grade)
    ((grade.val : ℝ) + loss) (gradeConstant grade) (nonnegative grade) (gradeBound point grade)

omit [TopologicalSpace Parameter] in
theorem originalNewtonBranch_uniform (grade : AdmissibleGrade) :
    TendstoUniformly
      (fun index point => stateSmoothEmbedding parameters reference inside grade.val grade.property
        ((data point).iterate index).toCore)
      (fun point => stateSmoothEmbedding parameters reference inside grade.val grade.property
        (originalNewtonLimit parameters reference inside low (data point) gradeConstant nonnegative (gradeBound point))) atTop := by
  have same := funext (fun point => originalNewtonBranch_grade_limit parameters reference inside low
    data gradeConstant nonnegative gradeBound point grade)
  rw [same]
  exact uniformGuardedGradeConvergence data (originalNewtonGradeMap parameters reference inside low grade)
    ((grade.val : ℝ) + loss) (gradeConstant grade) (nonnegative grade) (fun point => gradeBound point grade)

/-- Uniform tails prove continuity of the SAME smooth branch in every actual
completed grade. Smoothness of the infinite limit is not inferred here. -/
theorem originalNewtonBranch_continuous (grade : AdmissibleGrade)
    (finiteContinuous : ∀ index, Continuous (fun point =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property ((data point).iterate index).toCore)) :
    Continuous (fun point => stateSmoothEmbedding parameters reference inside grade.val grade.property
      (originalNewtonLimit parameters reference inside low (data point) gradeConstant nonnegative (gradeBound point))) := by
  have uniform := originalNewtonBranch_uniform parameters reference inside low data gradeConstant nonnegative gradeBound grade
  apply continuousOn_univ.mp
  apply (tendstoUniformlyOn_univ.mpr uniform).continuousOn
  exact Filter.Frequently.of_forall (fun index => (finiteContinuous index).continuousOn)

end Grad.NashMoser.OriginalLimit
