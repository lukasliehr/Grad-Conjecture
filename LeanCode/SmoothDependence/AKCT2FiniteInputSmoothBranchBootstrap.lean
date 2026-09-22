import AKCT1BranchDerivativeLowAbsorption
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff

namespace Grad.NashMoser.BranchDerivative

/-- The final NM11 induction: first derivatives represented by finite-input
Banach maps bootstrap the SAME branch to every finite order on the SAME open
set. The input grade can depend on the tested order and output grade. -/
theorem allGrade_contDiffOn_of_finite_input_derivative
    {Parameter Index : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (Grade : Index → Type*) [∀ index, NormedAddCommGroup (Grade index)]
    [∀ index, NormedSpace ℝ (Grade index)]
    (domain : Set Parameter) (openDomain : IsOpen domain)
    (branch : ∀ index, Parameter → Grade index)
    (derivative : ∀ index, Parameter → Parameter →L[ℝ] Grade index)
    (hasDerivative : ∀ index point, point ∈ domain → HasFDerivAt (branch index) (derivative index point) point)
    (realizations : ∀ (order : ℕ) (index : Index),
      ∃ (input : Index) (neighborhood : Set (Parameter × Grade input))
        (realization : Parameter × Grade input → Parameter →L[ℝ] Grade index),
        MapsTo (fun point => (point, branch input point)) domain neighborhood ∧
        ContDiffOn ℝ order realization neighborhood ∧
        ∀ point ∈ domain, derivative index point = realization (point, branch input point)) :
    ∀ index, ContDiffOn ℝ ∞ (branch index) domain := by
  have finite : ∀ order : ℕ, ∀ index, ContDiffOn ℝ order (branch index) domain := by
    intro order
    induction order with
    | zero =>
      intro index
      apply contDiffOn_zero.mpr
      intro point member
      exact (hasDerivative index point member).continuousAt.continuousWithinAt
    | succ order induction =>
      intro index
      obtain ⟨input, neighborhood, realization, maps, smooth, same⟩ := realizations order index
      have composed : ContDiffOn ℝ order (fun point => realization (point, branch input point)) domain :=
        smooth.comp (contDiffOn_id.prodMk (induction input)) maps
      have derivativeSmooth : ContDiffOn ℝ order (derivative index) domain :=
        composed.congr (fun point member => same point member)
      rw [show ((order+1 : ℕ) : ℕ∞ω) = (order : ℕ∞ω)+1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn openDomain.uniqueDiffOn).mpr
      refine ⟨?_, derivative index, derivativeSmooth, ?_⟩
      · intro impossible
        simp at impossible
      · intro point member
        exact (hasDerivative index point member).hasFDerivWithinAt
  intro index
  exact contDiffOn_infty.mpr (fun order => finite order index)

end Grad.NashMoser.BranchDerivative
