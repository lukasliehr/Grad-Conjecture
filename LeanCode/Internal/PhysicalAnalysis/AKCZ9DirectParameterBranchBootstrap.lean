import AKCZ8FiniteLossInverseSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped Topology ContDiff
namespace Grad.NashMoser.InverseCalculus

/-- Direct NM11 bootstrap along the SAME finite-parameter branch. The
finite-loss resolvent theorem supplies inverse regularity at each induction
step; no extension over completed base states is required. -/
theorem allGradeBranch_contDiffOn_of_shifted_inverse
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (State Source : ℕ → Type*)
    [∀ grade, NormedAddCommGroup (State grade)] [∀ grade, NormedSpace ℝ (State grade)]
    [∀ grade, NormedAddCommGroup (Source grade)] [∀ grade, NormedSpace ℝ (Source grade)]
    (domain : Set Parameter) (openDomain : IsOpen domain) (forwardLoss inverseLoss : ℕ)
    (branch : ∀ grade, Parameter → State grade)
    (branchDerivative : ∀ grade, Parameter → Parameter →L[ℝ] State grade)
    (hasDerivative : ∀ grade point, point ∈ domain → HasFDerivAt (branch grade) (branchDerivative grade point) point)
    (forward : ∀ grade, Parameter → State (grade+forwardLoss) →L[ℝ] Source grade)
    (parameterDerivative : ∀ grade, Parameter → Parameter →L[ℝ] Source grade)
    (inverse : ∀ output input, Parameter → Source input →L[ℝ] State output)
    (continuous : ∀ output, ∃ input, output+inverseLoss ≤ input ∧ ContinuousOn (inverse output input) domain)
    (resolvent : ∀ output middle input, output+inverseLoss ≤ middle → middle+forwardLoss+inverseLoss ≤ input →
      ∀ base ∈ domain, ∀ point ∈ domain,
      inverse output input point-inverse output input base =
        -(inverse output middle point).comp ((forward middle point-forward middle base).comp
          (inverse (middle+forwardLoss) input base)))
    (forwardRegular : ∀ order : ℕ, (∀ grade, ContDiffOn ℝ order (branch grade) domain) →
      ∀ grade, ContDiffOn ℝ order (forward grade) domain)
    (parameterRegular : ∀ order : ℕ, (∀ grade, ContDiffOn ℝ order (branch grade) domain) →
      ∀ grade, ContDiffOn ℝ order (parameterDerivative grade) domain)
    (formula : ∀ output input, output+inverseLoss ≤ input → ∀ point ∈ domain,
      branchDerivative output point = -(inverse output input point).comp (parameterDerivative input point)) :
    ∀ grade, ContDiffOn ℝ ∞ (branch grade) domain := by
  have finite : ∀ order : ℕ, ∀ grade, ContDiffOn ℝ order (branch grade) domain := by
    intro order
    induction order with
    | zero =>
      intro grade
      apply contDiffOn_zero.mpr
      intro point member
      exact (hasDerivative grade point member).continuousAt.continuousWithinAt
    | succ order previous =>
      intro grade
      obtain ⟨input,ordered,inverseSmooth⟩ := finiteLossInverse_contDiffOn State Source domain openDomain
        forwardLoss inverseLoss forward inverse continuous resolvent order (forwardRegular order previous) grade
      have derivativeSmooth : ContDiffOn ℝ order (branchDerivative grade) domain :=
        (inverseSmooth.clm_comp (parameterRegular order previous input)).neg.congr
          (fun point member => formula grade input ordered point member)
      rw [show ((order+1 : ℕ) : ℕ∞ω) = (order : ℕ∞ω)+1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn openDomain.uniqueDiffOn).mpr
      refine ⟨by simp,branchDerivative grade,derivativeSmooth,?_⟩
      intro point member
      exact (hasDerivative grade point member).hasFDerivWithinAt
  intro grade
  exact contDiffOn_infty.mpr (fun order => finite order grade)

end Grad.NashMoser.InverseCalculus
