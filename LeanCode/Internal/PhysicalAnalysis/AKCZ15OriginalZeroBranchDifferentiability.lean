import AKCZ14OriginalZeroBranchDerivativeFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology
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

include left in
/-- The actual original zero branch is differentiable in every completed
grade. Its continuity and one-high inverse bound supply the nonlinear
remainder estimate through accepted CV15; no derivative premise is used. -/
theorem originalZeroBranch_hasFDerivAt (openDomain : IsOpen domain)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain)
    (zeros : ∀ point ∈ domain, originalNonlinearSource parameters cellLength reference insideR point (branch point)=0) :
    ∀ grade point, point ∈ domain →
      HasFDerivAt (fun point => stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (branch point))
        (originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength grade point) point := by
  let : ∀ grade, NormedSpace ℝ (stateRange parameters reference insideR (grade+4) (branchGrade_large grade)) :=
    fun grade => inferInstance
  apply allGrade_hasFDerivAt_of_inverse_remainder
    (fun grade => stateRange parameters reference insideR (grade+4) (branchGrade_large grade)) domain openDomain 0
    (fun grade point => stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (branch point))
    continuous (originalZeroBranchDerivative parameters reference insideR branch domain loss inverse constant nonnegative tame cellLength)
  intro base member grade
  obtain ⟨remainderConstant,_,bound⟩ := originalBranch_inverseTaylor parameters cellLength reference insideR
    (grade+loss+4) (by omega) (grade+4) (branchGrade_large grade) branch base
    (admissible base member).1 (admissible base member).2
    ((continuous (grade+loss+6) base member).continuousAt (openDomain.mem_nhds member))
    (inverse base) (constant grade*(2+‖stateSmoothEmbedding parameters reference insideR (grade+loss+4)
      (branchGrade_large (grade+loss)) (branch base)‖)) 0
    (mul_nonneg (nonnegative grade) (by positivity)) (le_refl 0) (by
      intro source
      simpa only [zero_mul,add_zero] using
        originalTameInverse_singleGrade parameters reference insideR branch domain loss inverse constant nonnegative tame
          grade (grade+loss) (le_refl _) base member source)
  refine ⟨grade+loss+6,remainderConstant,?_⟩
  filter_upwards [bound,openDomain.mem_nhds member] with point estimate pointMember
  rw [originalZeroBranchDerivative_remainder_norm parameters reference insideR branch domain loss inverse constant nonnegative tame
    cellLength admissible left grade base member point (zeros base member) (zeros point pointMember)]
  have highSub := map_sub (stateSmoothEmbedding parameters reference insideR (grade+loss+4+6)
    (realHighLarge (grade+loss+4))) (branch point) (branch base)
  have lowSub := map_sub (stateSmoothEmbedding parameters reference insideR 4 realLowLarge) (branch point) (branch base)
  rw [highSub,lowSub] at estimate
  exact estimate

end Grad.NashMoser.InverseCalculus
