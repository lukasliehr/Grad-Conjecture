import SK2Interface
import SK1Proof
import Mathlib.Tactic.NormNum

noncomputable section

open scoped BigOperators Topology

namespace Grad.SchurKernel.Discrete

theorem lp_norm_sq {Value : Type*} [NormedAddCommGroup Value]
    (field : lp (fun _ : ℤ => Value) 2) :
    ‖field‖ ^ 2 = ∑' cell : ℤ, ‖field cell‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field

theorem lp_sum_sq_le {Value : Type*} [NormedAddCommGroup Value]
    (field : lp (fun _ : ℤ => Value) 2) (cells : Finset ℤ) :
    ∑ cell ∈ cells, ‖field cell‖ ^ 2 ≤ ‖field‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) field cells

section Generic

variable {ValueIn ValueOut : Type*}
  [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
  [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]

theorem row_norm_summable (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (majorant : ℤ → ℤ → ℝ)
    (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
    (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
    (rowsSummable : ∀ output, Summable (majorant output))
    (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ) :
    Summable (fun input : ℤ => ‖coefficients output input (field input)‖) := by
  refine Summable.of_norm_bounded (Summable.mul_right ‖field‖ (rowsSummable output)) ?_
  intro input
  rw [norm_norm]
  exact ((coefficients output input).le_opNorm (field input)).trans
    ((mul_le_mul_of_nonneg_right (domination output input) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (p := 2) (by norm_num) field input)
        (majorantNonnegative output input)))

theorem row_summable [CompleteSpace ValueOut]
    (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (majorant : ℤ → ℤ → ℝ)
    (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
    (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
    (rowsSummable : ∀ output, Summable (majorant output))
    (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ) :
    Summable (fun input : ℤ => coefficients output input (field input)) :=
  (row_norm_summable coefficients majorant majorantNonnegative domination
    rowsSummable field output).of_norm

section Bounds

variable (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
  (majorant : ℤ → ℤ → ℝ) (rowBound columnBound : ℝ)
  (rowNonnegative : 0 ≤ rowBound) (columnNonnegative : 0 ≤ columnBound)
  (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
  (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
  (rowsSummable : ∀ output, Summable (majorant output))
  (columnsSummable : ∀ input, Summable (fun output => majorant output input))
  (rows : ∀ output, ∑' input : ℤ, majorant output input ≤ rowBound)
  (columns : ∀ input, ∑' output : ℤ, majorant output input ≤ columnBound)

include coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
  majorantNonnegative domination rowsSummable columnsSummable rows columns

theorem finiteRectangle_sum_sq_le (field : lp (fun _ : ℤ => ValueIn) 2)
    (outputs inputs : Finset ℤ) :
    ∑ output ∈ outputs, ‖∑ input ∈ inputs, coefficients output input (field input)‖ ^ 2 ≤
      rowBound * columnBound * ‖field‖ ^ 2 := by
  classical
  have finiteRows (output : outputs) :
      ∑ input : inputs, majorant output input ≤ rowBound := by
    rw [Finset.sum_coe_sort]
    exact (Summable.sum_le_tsum inputs (fun input _membership =>
      majorantNonnegative output input) (rowsSummable output)).trans (rows output)
  have finiteColumns (input : inputs) :
      ∑ output : outputs, majorant output input ≤ columnBound := by
    rw [Finset.sum_coe_sort outputs (fun output : ℤ => majorant output input)]
    exact (Summable.sum_le_tsum outputs (fun output _membership =>
      majorantNonnegative output input) (columnsSummable input)).trans (columns input)
  have finiteBound := Grad.SchurKernel.Finite.finiteAction_sum_sq_le
    (fun (output : outputs) (input : inputs) => coefficients output input)
    (fun (output : outputs) (input : inputs) => majorant output input)
    rowBound columnBound rowNonnegative columnNonnegative
    (fun output input => majorantNonnegative output input)
    (fun output input => domination output input) finiteRows finiteColumns
    (WithLp.toLp 2 (fun input : inputs => field input) : PiLp 2 (fun _ : inputs => ValueIn))
  change (∑ output : outputs,
      ‖∑ input : inputs, coefficients output input (field input)‖ ^ 2) ≤
    rowBound * columnBound * ∑ input : inputs, ‖field input‖ ^ 2 at finiteBound
  have sumInputs (output : ℤ) :
      ∑ input : inputs, coefficients output input (field input) =
        ∑ input ∈ inputs, coefficients output input (field input) :=
    Finset.sum_coe_sort inputs (fun input : ℤ => coefficients output input (field input))
  simp_rw [sumInputs] at finiteBound
  rw [Finset.sum_coe_sort outputs (fun output : ℤ =>
      ‖∑ input ∈ inputs, coefficients output input (field input)‖ ^ 2),
    Finset.sum_coe_sort inputs (fun input : ℤ => ‖field input‖ ^ 2)] at finiteBound
  exact finiteBound.trans (mul_le_mul_of_nonneg_left (lp_sum_sq_le field inputs)
    (mul_nonneg rowNonnegative columnNonnegative))

variable [CompleteSpace ValueOut]

theorem discreteAction_finite_sum_sq_le (field : lp (fun _ : ℤ => ValueIn) 2)
    (outputs : Finset ℤ) :
    ∑ output ∈ outputs, ‖discreteAction coefficients field output‖ ^ 2 ≤
      rowBound * columnBound * ‖field‖ ^ 2 := by
  have limit := tendsto_finsetSum outputs fun output _membership =>
    (row_summable coefficients majorant majorantNonnegative domination
      rowsSummable field output).hasSum.norm.pow 2
  exact le_of_tendsto limit (Filter.Eventually.of_forall fun inputs =>
    finiteRectangle_sum_sq_le coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rowsSummable columnsSummable
      rows columns field outputs inputs)

theorem discreteAction_memLp (field : lp (fun _ : ℤ => ValueIn) 2) :
    Memℓp (discreteAction coefficients field) 2 := by
  apply memℓp_gen' (C := rowBound * columnBound * ‖field‖ ^ 2)
  intro outputs
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    discreteAction_finite_sum_sq_le coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rowsSummable columnsSummable
      rows columns field outputs

theorem discreteAction_tsum_sq_le_norm_sq (field : lp (fun _ : ℤ => ValueIn) 2) :
    ∑' output : ℤ, ‖discreteAction coefficients field output‖ ^ 2 ≤
      rowBound * columnBound * ‖field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _output => sq_nonneg _)
    (fun outputs => discreteAction_finite_sum_sq_le coefficients majorant rowBound columnBound
      rowNonnegative columnNonnegative majorantNonnegative domination rowsSummable
      columnsSummable rows columns field outputs)

theorem discreteAction_tsum_sq_le (field : lp (fun _ : ℤ => ValueIn) 2) :
    ∑' output : ℤ, ‖discreteAction coefficients field output‖ ^ 2 ≤
      rowBound * columnBound * ∑' input : ℤ, ‖field input‖ ^ 2 := by
  rw [← lp_norm_sq field]
  exact discreteAction_tsum_sq_le_norm_sq coefficients majorant rowBound columnBound
    rowNonnegative columnNonnegative majorantNonnegative domination rowsSummable
    columnsSummable rows columns field

def discreteActionLp (field : lp (fun _ : ℤ => ValueIn) 2) : lp (fun _ : ℤ => ValueOut) 2 :=
  ⟨discreteAction coefficients field,
    discreteAction_memLp coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rowsSummable columnsSummable
      rows columns field⟩

theorem discreteActionLp_apply (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ) :
    discreteActionLp coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field output =
        discreteAction coefficients field output := rfl

theorem norm_sq_discreteActionLp_le (field : lp (fun _ : ℤ => ValueIn) 2) :
    ‖discreteActionLp coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field‖ ^ 2 ≤
        rowBound * columnBound * ‖field‖ ^ 2 := by
  rw [lp_norm_sq]
  exact discreteAction_tsum_sq_le_norm_sq coefficients majorant rowBound columnBound
    rowNonnegative columnNonnegative majorantNonnegative domination rowsSummable
    columnsSummable rows columns field

theorem norm_discreteActionLp_le (field : lp (fun _ : ℤ => ValueIn) 2) :
    ‖discreteActionLp coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field‖ ≤
        Real.sqrt (rowBound * columnBound) * ‖field‖ := by
  have bound := Real.le_sqrt_of_sq_le
    (norm_sq_discreteActionLp_le coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rowsSummable columnsSummable
      rows columns field)
  rw [Real.sqrt_mul (mul_nonneg rowNonnegative columnNonnegative),
    Real.sqrt_sq (norm_nonneg field)] at bound
  exact bound

end Bounds
end Generic
end Grad.SchurKernel.Discrete
