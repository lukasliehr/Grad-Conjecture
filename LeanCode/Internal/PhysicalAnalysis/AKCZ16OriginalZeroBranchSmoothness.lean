import AKCZ15OriginalZeroBranchDifferentiability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff
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

include right left nonnegative tame in
/-- Full parameter smoothness of the SAME original continuous zero branch
from the actual two-sided tame inverse. QYP supplies forward regularity,
CV15 supplies the genuine first derivative, and shifted resolvent induction
supplies every higher order on the SAME open parameter domain. -/
theorem originalZeroBranch_contDiffOn (openDomain : IsOpen domain)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain)
    (zeros : ∀ point ∈ domain, originalNonlinearSource parameters cellLength reference insideR point (branch point)=0) :
    ∀ grade, ContDiffOn ℝ ∞ (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain := by
  let : ∀ grade, NormedSpace ℝ (stateRange parameters reference insideR (grade+4) (branchGrade_large grade)) :=
    fun grade => inferInstance
  let : ∀ grade, NormedSpace ℝ (sourceRange parameters (grade+4) (branchGrade_large grade)) :=
    fun grade => inferInstance
  apply allGradeBranch_contDiffOn_of_shifted_inverse
    (fun grade => stateRange parameters reference insideR (grade+4) (branchGrade_large grade))
    (fun grade => sourceRange parameters (grade+4) (branchGrade_large grade)) domain openDomain 6 loss
    (fun grade point => stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (branch point))
    (originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength)
    (originalZeroBranch_hasFDerivAt parameters reference insideR branch domain loss inverse constant nonnegative tame
      cellLength admissible left openDomain continuous zeros)
    (fun grade => originalBranchForward parameters cellLength reference insideR branch (grade+4) (branchGrade_large grade))
    (fun grade => originalBranchParameterDerivative parameters cellLength reference insideR branch (grade+4) (branchGrade_large grade))
    (originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame)
    (originalCompletedBranchInverse_continuous parameters reference insideR branch domain loss inverse constant nonnegative tame
      cellLength admissible right left openDomain continuous)
    (originalCompletedBranchInverse_resolvent parameters reference insideR branch domain loss inverse constant nonnegative tame
      cellLength admissible right left)
  · intro order previous grade
    exact (originalBranch_derivativeFactors_contDiffOn parameters cellLength reference insideR branch (grade+4)
      (branchGrade_large grade) order domain admissible (previous (grade+6))).1
  · intro order previous grade
    exact (originalBranch_derivativeFactors_contDiffOn parameters cellLength reference insideR branch (grade+4)
      (branchGrade_large grade) order domain admissible (previous (grade+6))).2
  · exact originalZeroBranchDerivative_formula parameters reference insideR branch domain loss inverse constant nonnegative tame
      cellLength admissible

end Grad.NashMoser.InverseCalculus
