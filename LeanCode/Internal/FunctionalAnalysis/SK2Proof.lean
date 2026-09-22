import SK2Estimates

noncomputable section

open scoped BigOperators

namespace Grad.SchurKernel.Discrete

variable {ValueIn ValueOut : Type*}
  [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
  [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut] [CompleteSpace ValueOut]

theorem discreteAction_add (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (majorant : ℤ → ℤ → ℝ)
    (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
    (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
    (rowsSummable : ∀ output, Summable (majorant output))
    (first second : lp (fun _ : ℤ => ValueIn) 2) :
    discreteAction coefficients (first + second) =
      discreteAction coefficients first + discreteAction coefficients second := by
  funext output
  change (∑' input : ℤ, coefficients output input (first input + second input)) =
    (∑' input : ℤ, coefficients output input (first input)) +
      ∑' input : ℤ, coefficients output input (second input)
  simp_rw [map_add]
  exact (row_summable coefficients majorant majorantNonnegative domination
    rowsSummable first output).tsum_add
      (row_summable coefficients majorant majorantNonnegative domination rowsSummable second output)

theorem discreteAction_smul (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (majorant : ℤ → ℤ → ℝ)
    (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
    (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
    (rowsSummable : ∀ output, Summable (majorant output))
    (scalar : ℂ) (field : lp (fun _ : ℤ => ValueIn) 2) :
    discreteAction coefficients (scalar • field) = scalar • discreteAction coefficients field := by
  funext output
  change (∑' input : ℤ, coefficients output input (scalar • field input)) =
    scalar • ∑' input : ℤ, coefficients output input (field input)
  simp_rw [map_smul]
  exact Summable.tsum_const_smul scalar
    (row_summable coefficients majorant majorantNonnegative domination rowsSummable field output)

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

def discreteActionLinear : lp (fun _ : ℤ => ValueIn) 2 →ₗ[ℂ] lp (fun _ : ℤ => ValueOut) 2 where
  toFun := discreteActionLp coefficients majorant rowBound columnBound rowNonnegative
    columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns
  map_add' first second := lp.ext
    (discreteAction_add coefficients majorant majorantNonnegative domination rowsSummable first second)
  map_smul' scalar field := lp.ext
    (discreteAction_smul coefficients majorant majorantNonnegative domination rowsSummable scalar field)

def discreteActionCLM : lp (fun _ : ℤ => ValueIn) 2 →L[ℂ] lp (fun _ : ℤ => ValueOut) 2 :=
  (discreteActionLinear coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
    majorantNonnegative domination rowsSummable columnsSummable rows columns).mkContinuous
      (Real.sqrt (rowBound * columnBound))
      (norm_discreteActionLp_le coefficients majorant rowBound columnBound rowNonnegative
        columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns)

theorem discreteActionCLM_apply (field : lp (fun _ : ℤ => ValueIn) 2) :
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field =
    discreteActionLp coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field := rfl

theorem discreteActionCLM_apply_coordinate (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ) :
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field output =
        ∑' input : ℤ, coefficients output input (field input) := rfl

theorem norm_sq_discreteActionCLM_le (field : lp (fun _ : ℤ => ValueIn) 2) :
    ‖discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field‖ ^ 2 ≤
        rowBound * columnBound * ‖field‖ ^ 2 :=
  norm_sq_discreteActionLp_le coefficients majorant rowBound columnBound rowNonnegative
    columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns field

theorem norm_discreteActionCLM_apply_le (field : lp (fun _ : ℤ => ValueIn) 2) :
    ‖discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns field‖ ≤
        Real.sqrt (rowBound * columnBound) * ‖field‖ :=
  norm_discreteActionLp_le coefficients majorant rowBound columnBound rowNonnegative
    columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns field

theorem norm_discreteActionCLM_le :
    ‖discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns‖ ≤
        Real.sqrt (rowBound * columnBound) :=
  (discreteActionLinear coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
    majorantNonnegative domination rowsSummable columnsSummable rows columns).mkContinuous_norm_le
      (Real.sqrt_nonneg (rowBound * columnBound))
      (norm_discreteActionLp_le coefficients majorant rowBound columnBound rowNonnegative
        columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns)

theorem discreteActionCLM_add (first second : lp (fun _ : ℤ => ValueIn) 2) :
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns (first + second) =
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns first +
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns second :=
  map_add _ _ _

theorem discreteActionCLM_smul (scalar : ℂ) (field : lp (fun _ : ℤ => ValueIn) 2) :
    discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
      majorantNonnegative domination rowsSummable columnsSummable rows columns (scalar • field) =
    scalar • discreteActionCLM coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rowsSummable columnsSummable rows columns field :=
  map_smul _ _ _

end Bounds
end Grad.SchurKernel.Discrete
