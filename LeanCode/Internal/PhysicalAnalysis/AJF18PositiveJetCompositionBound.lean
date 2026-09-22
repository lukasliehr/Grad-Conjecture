import AJF17MappedOrderedDerivatives
import GC15BudgetAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff BigOperators
namespace Grad.AnnularOrbitGenerators

/-- Order zero is uniformly bounded; positive coefficient derivatives
carry exactly one original physical budget. -/
def positiveJetBudget (budget : ℕ → ℝ) (order : ℕ) : ℝ := if order = 0 then 1 else budget order

theorem positiveJetBudget_nonnegative (budget : ℕ → ℝ) (nonnegative : ∀ order, 0 ≤ budget order) (order : ℕ) :
    0 ≤ positiveJetBudget budget order := by
  unfold positiveJetBudget
  split_ifs
  · norm_num
  · exact nonnegative order

theorem positiveJetBudget_pair (budget pair : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ budget order) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ first second, budget first * budget second ≤ pair (first + second) * budget (first + second))
    (first second : ℕ) (positive : 0 < first + second) :
    positiveJetBudget budget first * positiveJetBudget budget second ≤
      (1 + pair (first + second)) * budget (first + second) := by
  by_cases firstZero : first = 0
  · subst first
    have secondNonzero : second ≠ 0 := by omega
    have scalar : budget second ≤ (1 + pair second) * budget second :=
      le_mul_of_one_le_left (nonnegative second) (by linarith only [pairNonnegative second])
    simpa [positiveJetBudget, secondNonzero] using scalar
  by_cases secondZero : second = 0
  · subst second
    have scalar : budget first ≤ (1 + pair first) * budget first :=
      le_mul_of_one_le_left (nonnegative first) (by linarith only [pairNonnegative first])
    simpa [positiveJetBudget, firstZero] using scalar
  simp only [positiveJetBudget, if_neg firstZero, if_neg secondZero]
  exact (paired first second).trans (mul_le_mul_of_nonneg_right (by linarith) (nonnegative _))

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Binomial differentiation and original-budget interpolation preserve one
high factor under actual operator composition, including the two endpoint
terms with a bounded order-zero factor. -/
theorem iteratedDeriv_realComposition_oneHigh (outer : ℝ → F →L[ℝ] G) (inner : ℝ → E →L[ℝ] F)
    (outerSmooth : ContDiff ℝ ∞ outer) (innerSmooth : ContDiff ℝ ∞ inner)
    (budget pair outerConstant innerConstant : ℕ → ℝ)
    (budgetNonnegative : ∀ order, 0 ≤ budget order) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (outerNonnegative : ∀ order, 0 ≤ outerConstant order) (innerNonnegative : ∀ order, 0 ≤ innerConstant order)
    (paired : ∀ first second, budget first * budget second ≤ pair (first + second) * budget (first + second))
    (order : ℕ) (positive : 0 < order) (time : ℝ)
    (outerBound : ∀ index, index ≤ order → ‖iteratedDeriv index outer time‖ ≤ outerConstant index * positiveJetBudget budget index)
    (innerBound : ∀ index, index ≤ order → ‖iteratedDeriv index inner time‖ ≤ innerConstant index * positiveJetBudget budget index) :
    ‖iteratedDeriv order (fun parameter => (outer parameter).comp (inner parameter)) time‖ ≤
      (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        outerConstant index * innerConstant (order - index) * (1 + pair order)) * budget order := by
  apply (iteratedDeriv_realComposition_bound outer inner outerSmooth innerSmooth order time).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexLe : index ≤ order := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp member)
  have complementLe : order - index ≤ order := Nat.sub_le _ _
  have total : index + (order - index) = order := Nat.add_sub_of_le indexLe
  have factors := mul_le_mul (outerBound index indexLe) (innerBound (order - index) complementLe)
    (norm_nonneg _) (mul_nonneg (outerNonnegative index) (positiveJetBudget_nonnegative budget budgetNonnegative index))
  have budgetProduct := positiveJetBudget_pair budget pair budgetNonnegative pairNonnegative paired index (order - index)
    (by omega)
  rw [total] at budgetProduct
  have rearranged : ‖iteratedDeriv index outer time‖ * ‖iteratedDeriv (order - index) inner time‖ ≤
      (outerConstant index * innerConstant (order - index)) *
        (positiveJetBudget budget index * positiveJetBudget budget (order - index)) :=
    factors.trans_eq (by ring)
  have combined := rearranged.trans
    (mul_le_mul_of_nonneg_left budgetProduct (mul_nonneg (outerNonnegative index) (innerNonnegative (order - index))))
  have weighted := mul_le_mul_of_nonneg_left combined (by positivity : (0 : ℝ) ≤ order.choose index)
  simpa only [mul_assoc] using weighted

end Grad.AnnularOrbitGenerators
