import AKCZ13OriginalInverseNormContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 3500
open Set
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds Grad.SmoothForward
open Grad.NashMoser.OriginalLimit Grad.NashMoser.BranchDerivative

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference insideR)
    (domain : Set OriginalFiniteParameter) (loss : ℕ)
    (inverse : OriginalFiniteParameter → sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR)
    (constant : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constant grade)
    (tame : ∀ grade point, point ∈ domain → ∀ source,
      ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (inverse point source)‖ ≤
        constant grade*(‖sourceSmoothEmbedding parameters (grade+loss+4) (branchGrade_large (grade+loss)) source‖ +
          (1+‖stateSmoothEmbedding parameters reference insideR (grade+loss+4) (branchGrade_large (grade+loss)) (branch point)‖)*
            ‖sourceSmoothEmbedding parameters (loss+4) (branchGrade_large loss) source‖))

variable (cellLength : ℝ)
    (admissible : ∀ point ∈ domain, point.1 ∈ Seed.parameterDomain ∧
      ChartAxisCondition (smoothingChartCore parameters (branch point).val))
    (right : ∀ point (member : point ∈ domain), ∀ source,
      literalPhysicalSmoothForward parameters cellLength reference insideR point.1 (admissible point member).1
        (point.2,branch point) (admissible point member).2 (inverse point source) = source)
    (left : ∀ point (member : point ∈ domain), ∀ state,
      inverse point (literalPhysicalSmoothForward parameters cellLength reference insideR point.1 (admissible point member).1
        (point.2,branch point) (admissible point member).2 state) = state)

/-- The actual branch derivative candidate -V DqPhi, realized in the
original output grade and the minimal tame source grade. -/
def originalZeroBranchDerivative (grade : ℕ) (point : OriginalFiniteParameter) :
    OriginalFiniteParameter →L[ℝ] stateRange parameters reference insideR (grade+4) (branchGrade_large grade) :=
  -(originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame grade (grade+loss) point).comp
    (originalBranchParameterDerivative parameters cellLength reference insideR branch (grade+loss+4) (branchGrade_large (grade+loss)) point)

theorem originalZeroBranchDerivative_core (grade : ℕ) (point : OriginalFiniteParameter) (member : point ∈ domain)
    (direction : OriginalFiniteParameter) :
    originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength grade point direction =
      -stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade)
        (inverse point (originalParameterDerivative parameters reference insideR cellLength (point.1,point.2,branch point)
          (admissible point member).1 (admissible point member).2 direction)) := by
  simp only [originalZeroBranchDerivative,neg_apply,ContinuousLinearMap.comp_apply]
  rw [originalBranchParameterDerivative_core parameters cellLength reference insideR branch (grade+loss+4)
    (branchGrade_large (grade+loss)) point (admissible point member).1 (admissible point member).2,
    originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame
      grade (grade+loss) (le_refl _) point member]

include admissible in
/-- The candidate is independent of the chosen sufficient input grade.
This is the literal formula used by each finite-order inverse bootstrap. -/
theorem originalZeroBranchDerivative_formula (output input : ℕ) (ordered : output+loss ≤ input)
    (point : OriginalFiniteParameter) (member : point ∈ domain) :
    originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength output point =
      -(originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input point).comp
        (originalBranchParameterDerivative parameters cellLength reference insideR branch (input+4) (branchGrade_large input) point) := by
  apply ContinuousLinearMap.ext
  intro direction
  rw [originalZeroBranchDerivative_core parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength admissible
    output point member direction]
  simp only [neg_apply,ContinuousLinearMap.comp_apply]
  rw [originalBranchParameterDerivative_core parameters cellLength reference insideR branch (input+4)
    (branchGrade_large input) point (admissible point member).1 (admissible point member).2,
    originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame
      output input ordered point member]

include left in
/-- Exact difference of two original nonlinear zeros. The right side is
the SAME literal Taylor remainder to which accepted CV15 applies. -/
theorem originalZeroBranchDerivative_remainder_norm (grade : ℕ)
    (base : OriginalFiniteParameter) (baseMember : base ∈ domain)
    (point : OriginalFiniteParameter)
    (baseZero : originalNonlinearSource parameters cellLength reference insideR base (branch base)=0)
    (pointZero : originalNonlinearSource parameters cellLength reference insideR point (branch point)=0) :
    ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (branch point) -
      stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (branch base) -
        originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength grade base (point-base)‖ =
    ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade)
      (inverse base (originalLiteralTaylorRemainder parameters cellLength reference insideR (base.1,base.2,branch base)
        (admissible base baseMember).1 (admissible base baseMember).2 (point.1,point.2,branch point)))‖ := by
  have same := congrArg (fun state => ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) state‖)
    (inverse_two_zero_difference (originalNonlinearSource parameters cellLength reference insideR)
      base point (branch base) (branch point)
      (originalParameterDerivative parameters reference insideR cellLength (base.1,base.2,branch base)
        (admissible base baseMember).1 (admissible base baseMember).2)
      (literalPhysicalSmoothForward parameters cellLength reference insideR base.1 (admissible base baseMember).1
        (base.2,branch base) (admissible base baseMember).2)
      (inverse base) (left base baseMember) baseZero pointZero)
  change ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade)
    (branch point-branch base-(-inverse base (originalParameterDerivative parameters reference insideR cellLength
      (base.1,base.2,branch base) (admissible base baseMember).1 (admissible base baseMember).2 (point-base))))‖ =
    ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade)
      (-inverse base (originalLiteralTaylorRemainder parameters cellLength reference insideR (base.1,base.2,branch base)
        (admissible base baseMember).1 (admissible base baseMember).2 (point.1,point.2,branch point)))‖ at same
  have outerSub := map_sub (stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade))
    (branch point-branch base) (-inverse base (originalParameterDerivative parameters reference insideR cellLength
      (base.1,base.2,branch base) (admissible base baseMember).1 (admissible base baseMember).2 (point-base)))
  have branchSub := map_sub (stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade))
    (branch point) (branch base)
  have candidateNeg := map_neg (stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade))
    (inverse base (originalParameterDerivative parameters reference insideR cellLength
      (base.1,base.2,branch base) (admissible base baseMember).1 (admissible base baseMember).2 (point-base)))
  have remainderNeg := map_neg (stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade))
    (inverse base (originalLiteralTaylorRemainder parameters cellLength reference insideR (base.1,base.2,branch base)
      (admissible base baseMember).1 (admissible base baseMember).2 (point.1,point.2,branch point)))
  rw [outerSub,branchSub,candidateNeg,remainderNeg,norm_neg] at same
  rw [originalZeroBranchDerivative_core parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength admissible
    grade base baseMember (point-base)]
  exact same

end Grad.NashMoser.InverseCalculus
