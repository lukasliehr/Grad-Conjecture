import AKDN26ActualNativeRankAllocations

noncomputable section
set_option autoImplicit false
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation

/-- A finite collection of constants is bounded before any state or source
is chosen. This is used only to collect the actual derivative coefficients. -/
theorem finiteUniformMajorant {Index : Type*} [Fintype Index] (values : Index → ℝ) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ index, |values index| ≤ constant := by
  classical
  refine ⟨1+∑ index, |values index|, ?_, ?_⟩
  · have nonnegative : 0 ≤ ∑ index, |values index| :=
      Finset.sum_nonneg (fun index _ => abs_nonneg (values index))
    linarith
  · intro index
    have term : |values index| ≤ ∑ index, |values index| :=
      Finset.single_le_sum (fun index _ => abs_nonneg (values index)) (Finset.mem_univ index)
    linarith

/-- The two coefficient payments are interpolated at their exact sum,
before induction on the lower Euler derivative. The finite constant is
uniform in every split below the fixed output rank and every actual state. -/
theorem uniformReferencePhysicalBudget_pair (parameters : PhaseParameters) (offset total : ℕ) :
    ∃ constant : ℝ, 1 ≤ constant ∧
    ∀ (field : ACore parameters 3) (rho epsilon : ℝ),
    physicalBudget parameters field rho epsilon offset ≤ 1 →
    ∀ first second : ℕ, first+second ≤ total →
      (1+physicalBudget parameters field rho epsilon (offset+first)) *
        (1+physicalBudget parameters field rho epsilon (offset+second)) ≤
      constant*(1+physicalBudget parameters field rho epsilon (offset+(first+second))) := by
  obtain ⟨constant,constantOne,uniform⟩ := finiteUniformMajorant
    (fun rank : Fin (total+1) => 3+pairBudgetConstant offset rank.val 1)
  refine ⟨constant,constantOne,?_⟩
  intro field rho epsilon low first second allocated
  have bound := referencePhysicalBudget_pair parameters field rho epsilon offset (first+second)
    first second (le_refl _) low
  have coefficient : 3+pairBudgetConstant offset (first+second) 1 ≤ constant :=
    (le_abs_self _).trans (uniform ⟨first+second,by omega⟩)
  exact bound.trans (mul_le_mul_of_nonneg_right coefficient
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)))

end Grad.OriginalCartesianTameEstimate
