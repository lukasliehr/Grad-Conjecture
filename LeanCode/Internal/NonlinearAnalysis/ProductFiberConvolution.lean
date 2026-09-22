import ProductFiniteTensorSum
import ProductCoefficientJet

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

def cellAssignmentEquiv (arity : ℕ) (cell : ℤ) :
    CellAssignments (arity + 1) cell ≃ (Fin arity → ℤ) where
  toFun assignment := Fin.init assignment.val
  invFun cells := ⟨Fin.snoc cells (cell - ∑ index, cells index), by
    rw [Fin.sum_univ_castSucc]
    simp⟩
  left_inv assignment := by
    apply Subtype.ext
    have lastValue : cell - ∑ index : Fin arity, assignment.val index.castSucc =
        assignment.val (Fin.last arity) := by
      have total := assignment.property
      rw [Fin.sum_univ_castSucc] at total
      omega
    simpa only [Fin.init, lastValue] using Fin.snoc_init_self assignment.val
  right_inv cells := by simp

theorem cellAssignment_last (arity : ℕ) (cell : ℤ) (assignment : CellAssignments (arity + 1) cell) :
    assignment.val (Fin.last arity) = cell - ∑ index : Fin arity, assignment.val index.castSucc := by
  have total := assignment.property
  rw [Fin.sum_univ_castSucc] at total
  omega

/-- Literal fixed-sum fiber convolution, with its actual nonnegative l2
representative and l1/l2 estimate. -/
theorem fiber_convolution_exists {arity : ℕ}
    (sizes : Fin arity → ℤ → ℝ) (nonnegative : ∀ index cell, 0 ≤ sizes index cell)
    (summable : ∀ index, Summable (sizes index))
    (last : lp (fun _ : ℤ => ℝ) 2) (lastNonnegative : ∀ cell, 0 ≤ last cell) :
    ∃ output : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, HasSum (fun assignment : CellAssignments (arity + 1) cell =>
        (∏ index : Fin arity, sizes index (assignment.val index.castSucc)) *
          last (assignment.val (Fin.last arity))) (output cell)) ∧
      (∀ cell, 0 ≤ output cell) ∧
      ‖output‖ ≤ (∏ index, ∑' cell, sizes index cell) * ‖last‖ := by
  let kernel (cells : Fin arity → ℤ) (cell : ℤ) :=
    (∏ index, sizes index (cells index)) * last (cell - ∑ index, cells index)
  have kernelNonnegative (cells : Fin arity → ℤ) (cell : ℤ) : 0 ≤ kernel cells cell :=
    mul_nonneg (Finset.prod_nonneg (fun _ _ => nonnegative _ _)) (lastNonnegative _)
  obtain ⟨output, sums, bound⟩ := dominated_multicell_series sizes nonnegative summable last lastNonnegative
    kernel (fun cells cell => by rw [Real.norm_of_nonneg (kernelNonnegative cells cell)])
  refine ⟨output, ?_, ?_, bound⟩
  · intro cell
    have reindexed := (cellAssignmentEquiv arity cell).hasSum_iff.mpr (sums cell)
    have functionsEqual : ((fun cells => kernel cells cell) ∘ (cellAssignmentEquiv arity cell)) =
        (fun assignment : CellAssignments (arity + 1) cell =>
          (∏ index : Fin arity, sizes index (assignment.val index.castSucc)) *
            last (assignment.val (Fin.last arity))) := by
      funext assignment
      change (∏ index : Fin arity, sizes index (assignment.val index.castSucc)) *
        last (cell - ∑ index : Fin arity, assignment.val index.castSucc) = _
      rw [cellAssignment_last]
    rw [functionsEqual] at reindexed
    exact reindexed
  · intro cell
    rw [← (sums cell).tsum_eq]
    exact tsum_nonneg (fun cells => kernelNonnegative cells cell)

end Grad.NonlinearProduct
