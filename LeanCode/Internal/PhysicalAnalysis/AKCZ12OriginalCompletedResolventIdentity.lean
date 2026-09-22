import AKCZ11OriginalTameInverseCompletions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds Grad.SmoothForward
open Grad.NashMoser.OriginalLimit

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

/-- The actual completed forward agrees with the literal original core
operator in every grade of the branch scale. -/
theorem originalBranchForward_core (grade : ℕ) (point : OriginalFiniteParameter) (member : point ∈ domain)
    (state : stateSmoothRange parameters reference insideR) :
    originalBranchForward parameters cellLength reference insideR branch (grade+4) (branchGrade_large grade) point
      (stateSmoothEmbedding parameters reference insideR (grade+4+6) (realHighLarge (grade+4)) state) =
      sourceSmoothEmbedding parameters (grade+4) (branchGrade_large grade)
        (literalPhysicalSmoothForward parameters cellLength reference insideR point.1 (admissible point member).1
          (point.2,branch point) (admissible point member).2 state) := by
  rw [originalBranchForward_original parameters cellLength reference insideR branch (grade+4) (by omega)
    point (admissible point member).1 (admissible point member).2]
  exact literalPhysicalSmoothForward_completedCLM.1 parameters cellLength reference insideR point.1
    (admissible point member).1 (grade+4) (by omega) (point.2,branch point) (admissible point member).2 state

include right left in
/-- Both literal inverse identities give the SAME completed resolvent with
all original source/state grade losses visible. -/
theorem originalCompletedBranchInverse_resolvent (output middle input : ℕ)
    (middleOrdered : output+loss ≤ middle) (inputOrdered : middle+6+loss ≤ input)
    (base : OriginalFiniteParameter) (baseMember : base ∈ domain)
    (point : OriginalFiniteParameter) (pointMember : point ∈ domain) :
    originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input point -
      originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input base =
    -(originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output middle point).comp
      ((originalBranchForward parameters cellLength reference insideR branch (middle+4) (branchGrade_large middle) point -
        originalBranchForward parameters cellLength reference insideR branch (middle+4) (branchGrade_large middle) base).comp
          (originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame (middle+6) input base)) := by
  apply ContinuousLinearMap.ext
  intro source
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters (input+4) (branchGrade_large input))
    (isClosed_eq
      (originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input point -
        originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input base).continuous
      (-(originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output middle point).comp
        ((originalBranchForward parameters cellLength reference insideR branch (middle+4) (branchGrade_large middle) point -
          originalBranchForward parameters cellLength reference insideR branch (middle+4) (branchGrade_large middle) base).comp
            (originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame (middle+6) input base))).continuous) _ source
  intro core
  simp only [sub_apply,neg_apply,ContinuousLinearMap.comp_apply]
  rw [originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame output input (by omega) point pointMember,
    originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame output input (by omega) base baseMember,
    originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame (middle+6) input inputOrdered base baseMember,
    originalBranchForward_core parameters reference insideR branch domain cellLength admissible middle point pointMember,
    originalBranchForward_core parameters reference insideR branch domain cellLength admissible middle base baseMember]
  rw [← map_sub (sourceSmoothEmbedding parameters (middle+4) (branchGrade_large middle)),
    originalCompletedBranchInverse_core parameters reference insideR branch domain loss inverse constant nonnegative tame output middle middleOrdered point pointMember]
  rw [← map_sub (stateSmoothEmbedding parameters reference insideR (output+4) (branchGrade_large output)),
    ← map_neg (stateSmoothEmbedding parameters reference insideR (output+4) (branchGrade_large output))]
  apply congrArg (stateSmoothEmbedding parameters reference insideR (output+4) (branchGrade_large output))
  rw [map_sub,left point pointMember,right base baseMember]
  abel

end Grad.NashMoser.InverseCalculus
