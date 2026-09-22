import ProductInterface

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.NonlinearProduct

def cellShiftEquiv (shift : ℤ) : ℤ ≃ ℤ where
  toFun cell := cell - shift
  invFun cell := cell + shift
  left_inv cell := by simp
  right_inv cell := by simp

def shiftLp {Value : Type} [NormedAddCommGroup Value]
    (sequence : lp (fun _ : ℤ => Value) 2) (shift : ℤ) : lp (fun _ : ℤ => Value) 2 :=
  ⟨fun cell => sequence (cell - shift), by
    apply memℓp_gen
    exact (cellShiftEquiv shift).summable_iff.mpr
      ((lp.memℓp sequence).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

theorem shiftLp_norm {Value : Type} [NormedAddCommGroup Value]
    (sequence : lp (fun _ : ℤ => Value) 2) (shift : ℤ) :
    ‖shiftLp sequence shift‖ = ‖sequence‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (cellShiftEquiv shift).tsum_eq (fun cell => ‖sequence cell‖ ^ (2 : ℝ≥0∞).toReal)

/-- A kernel dominated by an l1 family of translates of one l2 sequence
has a genuine l2 sum. This includes cell-dependent phase multipliers. -/
theorem dominated_shift_series {Index Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (majorant : Index → ℝ) (majorantNonnegative : ∀ index, 0 ≤ majorant index)
    (majorantSummable : Summable majorant) (shift : Index → ℤ)
    (last : lp (fun _ : ℤ => ℝ) 2) (lastNonnegative : ∀ cell, 0 ≤ last cell)
    (kernel : Index → ℤ → Value)
    (kernelBound : ∀ index cell, ‖kernel index cell‖ ≤ majorant index * last (cell - shift index)) :
    ∃ output : lp (fun _ : ℤ => Value) 2,
      (∀ cell, HasSum (fun index => kernel index cell) (output cell)) ∧
      ‖output‖ ≤ (∑' index, majorant index) * ‖last‖ := by
  let comparison (index : Index) : lp (fun _ : ℤ => ℝ) 2 :=
    majorant index • shiftLp last (shift index)
  have pointBound (index : Index) (cell : ℤ) :
      ‖kernel index cell‖ ≤ ‖comparison index cell‖ := by
    change _ ≤ ‖majorant index * last (cell - shift index)‖
    rw [Real.norm_of_nonneg (mul_nonneg (majorantNonnegative _) (lastNonnegative _))]
    exact kernelBound index cell
  let rows (index : Index) : lp (fun _ : ℤ => Value) 2 :=
    ⟨kernel index, (lp.memℓp (comparison index)).mono' (pointBound index)⟩
  have rowBound (index : Index) : ‖rows index‖ ≤ majorant index * ‖last‖ := by
    calc
      _ ≤ ‖comparison index‖ := lp.norm_mono (by norm_num) (pointBound index)
      _ = _ := by rw [norm_smul, Real.norm_of_nonneg (majorantNonnegative _), shiftLp_norm]
  have rowNormSummable : Summable (fun index => ‖rows index‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) rowBound
      (majorantSummable.mul_right ‖last‖)
  refine ⟨∑' index, rows index, ?_, ?_⟩
  · intro cell
    exact (lp.evalCLM ℝ (fun _ : ℤ => Value) 2 cell).hasSum rowNormSummable.of_norm.hasSum
  · apply (norm_tsum_le_tsum_norm rowNormSummable).trans
    exact (rowNormSummable.tsum_le_tsum rowBound (majorantSummable.mul_right ‖last‖)).trans_eq
      (tsum_mul_right)

end Grad.NonlinearProduct
