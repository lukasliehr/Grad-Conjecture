import AKCT3ContinuousBranchInverseRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology ContDiff

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.NashMoser.Numeric Grad.NashMoser.BranchDerivative

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (low : AdmissibleGrade)
    {Parameter F : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
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

/-- The actual reconstructed original smooth core in each completed grade. -/
def originalNewtonCompletedBranch (grade : AdmissibleGrade) (point : Parameter) :
    stateRange parameters reference inside grade.val grade.property :=
  stateSmoothEmbedding parameters reference inside grade.val grade.property
    (originalNewtonLimit parameters reference inside low (data point) gradeConstant nonnegative (gradeBound point))

omit [NormedSpace ℝ Parameter] in
/-- Uniform Newton tails also give continuity on the actual parameter domain;
no continuity of the finite iterates outside that domain is required. -/
theorem originalNewtonCompletedBranch_continuousOn (domain : Set Parameter) (grade : AdmissibleGrade)
    (finiteContinuous : ∀ index, ContinuousOn (fun point =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property
        ((data point).iterate index).toCore) domain) :
    ContinuousOn (originalNewtonCompletedBranch parameters reference inside low data gradeConstant
      nonnegative gradeBound grade) domain := by
  have uniform := originalNewtonBranch_uniform parameters reference inside low data gradeConstant
    nonnegative gradeBound grade
  exact uniform.tendstoUniformlyOn.continuousOn
    (Filter.Frequently.of_forall finiteContinuous)

/-- NM10--NM11 for the SAME constructed original constrained Newton branch.
The numerical/grade correction bounds, actual inverse-Taylor remainder, and
finite-input derivative realization are explicit application obligations.
Neither branch differentiability nor its parameter smoothness is assumed. -/
theorem originalNewtonCompletedBranch_smooth
    (domain : Set Parameter) (openDomain : IsOpen domain)
    (finiteContinuous : ∀ (grade : AdmissibleGrade) index, ContinuousOn (fun point =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property
        ((data point).iterate index).toCore) domain)
    (derivative : ∀ grade : AdmissibleGrade,
      Parameter → Parameter →L[ℝ] stateRange parameters reference inside grade.val grade.property)
    (inverseRemainder : ∀ base ∈ domain, ∀ grade,
      ∃ (high : AdmissibleGrade) (constant : ℝ), ∀ᶠ point in 𝓝 base,
        ‖originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound grade point -
          originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound grade base -
            derivative grade base (point-base)‖ ≤
          constant * (‖point-base‖+
            ‖originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound high point -
              originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound high base‖) *
            (‖point-base‖+
              ‖originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound low point -
                originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound low base‖))
    (realizations : ∀ (order : ℕ) (grade : AdmissibleGrade),
      ∃ (input : AdmissibleGrade)
        (neighborhood : Set (Parameter × stateRange parameters reference inside input.val input.property))
        (realization : Parameter × stateRange parameters reference inside input.val input.property →
          Parameter →L[ℝ] stateRange parameters reference inside grade.val grade.property),
        MapsTo (fun point => (point,
          originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound input point))
          domain neighborhood ∧
        ContDiffOn ℝ order realization neighborhood ∧
        ∀ point ∈ domain, derivative grade point = realization (point,
          originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound input point)) :
    (∀ grade base, base ∈ domain →
      HasFDerivAt (originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound grade)
        (derivative grade base) base) ∧
    ∀ grade, ContDiffOn ℝ ∞
      (originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound grade) domain := by
  let _ : ∀ grade : AdmissibleGrade,
      NormedAddCommGroup (stateRange parameters reference inside grade.val grade.property) :=
    fun grade => inferInstance
  let _ : ∀ grade : AdmissibleGrade,
      NormedSpace ℝ (stateRange parameters reference inside grade.val grade.property) :=
    fun grade => inferInstance
  exact allGrade_contDiffOn_of_inverse_remainder
    (fun grade : AdmissibleGrade => stateRange parameters reference inside grade.val grade.property)
    domain openDomain low
    (originalNewtonCompletedBranch parameters reference inside low data gradeConstant nonnegative gradeBound)
    (fun grade => originalNewtonCompletedBranch_continuousOn parameters reference inside low data
      gradeConstant nonnegative gradeBound domain grade (finiteContinuous grade)) derivative inverseRemainder realizations

end Grad.NashMoser.OriginalLimit
