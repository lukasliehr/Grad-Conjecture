import AKCZ12OriginalCompletedResolventIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology
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

include right left in
/-- All-grade continuity of the actual branch makes the one-high state
factor locally bounded. The original shifted inverse is therefore operator
norm continuous after a finite input loss, before any branch derivative. -/
theorem originalCompletedBranchInverse_continuous
    (openDomain : IsOpen domain)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain) :
    ∀ output, ∃ input, output+loss ≤ input ∧
      ContinuousOn (originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input) domain := by
  intro output
  let middle := output+loss
  let input := middle+6+loss
  refine ⟨input,by omega,?_⟩
  intro base member
  let low := originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input
  let outer := originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output middle
  let forward := originalBranchForward parameters cellLength reference insideR branch (middle+4) (branchGrade_large middle)
  let inner := originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame (middle+6) input base
  let bound := fun point => constant output*(2+‖stateSmoothEmbedding parameters reference insideR
    (output+loss+4) (branchGrade_large (output+loss)) (branch point)‖)
  have boundContinuous : ContinuousAt bound base :=
    continuousAt_const.mul (continuousAt_const.add
      ((continuous (output+loss) base member).continuousAt (openDomain.mem_nhds member)).norm)
  have small : ∀ᶠ point in 𝓝 base, bound point < bound base+1 :=
    boundContinuous.eventually (gt_mem_nhds (lt_add_one (bound base)))
  have outerBound : ∀ᶠ point in 𝓝 base, ‖outer point‖ ≤ bound base+1 := by
    filter_upwards [openDomain.mem_nhds member,small] with point pointMember near
    exact (originalCompletedBranchInverse_norm_bound parameters reference insideR branch domain loss inverse constant nonnegative tame
      output middle (by rfl) point pointMember).trans near.le
  have forwardContinuous : ContinuousAt forward base := by
    have regular := (originalBranch_derivativeFactors_contDiffOn parameters cellLength reference insideR branch
      (middle+4) (branchGrade_large middle) 0 domain admissible (contDiffOn_zero.mpr (continuous (middle+6)))).1
    exact (regular.continuousOn base member).continuousAt (openDomain.mem_nhds member)
  have derived : ContinuousAt low base := shifted_resolvent_continuousAt low outer forward inner base
    (by
      filter_upwards [openDomain.mem_nhds member] with point pointMember
      exact originalCompletedBranchInverse_resolvent parameters reference insideR branch domain loss inverse constant nonnegative tame
        cellLength admissible right left output middle input (by rfl) (by rfl) base member point pointMember)
    (bound base+1) outerBound forwardContinuous
  exact derived.continuousWithinAt

end Grad.NashMoser.InverseCalculus
