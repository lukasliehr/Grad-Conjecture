import ProductSequenceConvolution

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

def splitCellsEquiv (arity : ℕ) : (Fin (arity + 1) → ℤ) ≃ ((Fin arity → ℤ) × ℤ) where
  toFun cells := (Fin.init cells, cells (Fin.last arity))
  invFun pair := Fin.snoc pair.1 pair.2
  left_inv cells := Fin.snoc_init_self cells
  right_inv pair := by ext <;> simp

theorem finite_tensor_hasSum (arity : ℕ) (sizes : Fin arity → ℤ → ℝ)
    (nonnegative : ∀ index cell, 0 ≤ sizes index cell)
    (summable : ∀ index, Summable (sizes index)) :
    HasSum (fun cells : Fin arity → ℤ => ∏ index, sizes index (cells index))
      (∏ index, ∑' cell, sizes index cell) := by
  induction arity with
  | zero =>
    have only : ∀ cells : Fin 0 → ℤ, cells = (fun _ => 0) := fun _ => Subsingleton.elim _ _
    simp [only]
  | succ arity inductionHypothesis =>
    have firstSum := inductionHypothesis (fun index => sizes index.castSucc)
      (fun index cell => nonnegative index.castSucc cell) (fun index => summable index.castSucc)
    have pairSummable : Summable (fun pair : (Fin arity → ℤ) × ℤ =>
        (∏ index, sizes index.castSucc (pair.1 index)) * sizes (Fin.last arity) pair.2) :=
      firstSum.summable.mul_of_nonneg (summable (Fin.last arity))
        (fun cells => Finset.prod_nonneg (fun index _ => nonnegative _ (cells index)))
        (nonnegative (Fin.last arity))
    have totalSummable : Summable (fun cells : Fin (arity + 1) → ℤ =>
        ∏ index, sizes index (cells index)) := by
      simpa [splitCellsEquiv, Fin.prod_univ_castSucc, Fin.init, Function.comp_def] using
        (splitCellsEquiv arity).summable_iff.mpr pairSummable
    apply totalSummable.hasSum_iff.mpr
    calc
      _ = ∑' pair : (Fin arity → ℤ) × ℤ,
          (∏ index, sizes index.castSucc (pair.1 index)) * sizes (Fin.last arity) pair.2 := by
        simpa [splitCellsEquiv, Fin.prod_univ_castSucc, Fin.init] using
          (splitCellsEquiv arity).tsum_eq (fun pair : (Fin arity → ℤ) × ℤ =>
            (∏ index, sizes index.castSucc (pair.1 index)) * sizes (Fin.last arity) pair.2)
      _ = (∏ index : Fin arity, ∑' cell, sizes index.castSucc cell) *
          (∑' cell, sizes (Fin.last arity) cell) := by
        rw [← firstSum.summable.tsum_mul_tsum (summable (Fin.last arity)) pairSummable,
          firstSum.tsum_eq]
      _ = _ := by rw [Fin.prod_univ_castSucc]

/-- All-arity l1/l2 convolution with no arity-dependent loss of derivatives. -/
theorem dominated_multicell_series {arity : ℕ} {Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (sizes : Fin arity → ℤ → ℝ) (nonnegative : ∀ index cell, 0 ≤ sizes index cell)
    (summable : ∀ index, Summable (sizes index))
    (last : lp (fun _ : ℤ => ℝ) 2) (lastNonnegative : ∀ cell, 0 ≤ last cell)
    (kernel : (Fin arity → ℤ) → ℤ → Value)
    (kernelBound : ∀ cells cell, ‖kernel cells cell‖ ≤
      (∏ index, sizes index (cells index)) * last (cell - ∑ index, cells index)) :
    ∃ output : lp (fun _ : ℤ => Value) 2,
      (∀ cell, HasSum (fun cells => kernel cells cell) (output cell)) ∧
      ‖output‖ ≤ (∏ index, ∑' cell, sizes index cell) * ‖last‖ := by
  have tensorSum := finite_tensor_hasSum arity sizes nonnegative summable
  simpa only [tensorSum.tsum_eq] using dominated_shift_series
    (fun cells : Fin arity → ℤ => ∏ index, sizes index (cells index))
    (fun cells => Finset.prod_nonneg (fun index _ => nonnegative _ (cells index)))
    tensorSum.summable (fun cells => ∑ index, cells index) last lastNonnegative kernel kernelBound

end Grad.NonlinearProduct
