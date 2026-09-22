import SK1Interface
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators

namespace Grad.SchurKernel.Finite

theorem weightedSum_sq_le {Index : Type*} [Fintype Index]
    (weight amplitude : Index → ℝ) (weightNonnegative : ∀ index, 0 ≤ weight index) :
    (∑ index, weight index * amplitude index) ^ 2 ≤
      (∑ index, weight index) * ∑ index, weight index * amplitude index ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := weight) (g := fun index => weight index * amplitude index ^ 2) ?_ ?_ ?_
  · intro index _membership
    exact weightNonnegative index
  · intro index _membership
    exact mul_nonneg (weightNonnegative index) (sq_nonneg _)
  · intro index _membership
    exact le_of_eq (by ring)

section Generic

variable {Output Input ValueIn ValueOut : Type*} [Fintype Output] [Fintype Input]
  [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
  [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]

omit [Fintype Output] in
theorem finiteAction_row_sq_le
    (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (majorant : Output → Input → ℝ) (rowBound : ℝ)
    (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
    (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
    (rows : ∀ output, ∑ input, majorant output input ≤ rowBound)
    (field : PiLp 2 (fun _ : Input => ValueIn)) (output : Output) :
    ‖finiteAction coefficients field output‖ ^ 2 ≤
      rowBound * ∑ input, majorant output input * ‖field input‖ ^ 2 := by
  have scalarBound : ‖finiteAction coefficients field output‖ ≤
      ∑ input, majorant output input * ‖field input‖ := by
    change ‖∑ input, coefficients output input (field input)‖ ≤ _
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro input _membership
    exact ((coefficients output input).le_opNorm (field input)).trans
      (mul_le_mul_of_nonneg_right (domination output input) (norm_nonneg _))
  calc
    _ ≤ (∑ input, majorant output input * ‖field input‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun input _membership =>
        mul_nonneg (majorantNonnegative output input) (norm_nonneg _))).mpr scalarBound
    _ ≤ (∑ input, majorant output input) *
        ∑ input, majorant output input * ‖field input‖ ^ 2 :=
      weightedSum_sq_le (majorant output) (fun input => ‖field input‖)
        (majorantNonnegative output)
    _ ≤ _ := mul_le_mul_of_nonneg_right (rows output)
      (Finset.sum_nonneg fun input _membership =>
        mul_nonneg (majorantNonnegative output input) (sq_nonneg _))

theorem finiteAction_sum_sq_le : sumSquaresGoal (Output := Output) (Input := Input)
    (ValueIn := ValueIn) (ValueOut := ValueOut) := by
  intro coefficients majorant rowBound columnBound rowNonnegative _columnNonnegative
    majorantNonnegative domination rows columns field
  calc
    _ ≤ ∑ output, rowBound * ∑ input, majorant output input * ‖field input‖ ^ 2 :=
      Finset.sum_le_sum fun output _membership =>
        finiteAction_row_sq_le coefficients majorant rowBound majorantNonnegative
          domination rows field output
    _ = rowBound * ∑ input, (∑ output, majorant output input) * ‖field input‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ rowBound * ∑ input, columnBound * ‖field input‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun input _membership =>
        mul_le_mul_of_nonneg_right (columns input) (sq_nonneg _)) rowNonnegative
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem finiteAction_norm_le : normGoal (Output := Output) (Input := Input)
    (ValueIn := ValueIn) (ValueOut := ValueOut) := by
  intro coefficients majorant rowBound columnBound rowNonnegative columnNonnegative
    majorantNonnegative domination rows columns field
  have squareBound : ‖finiteAction coefficients field‖ ^ 2 ≤
      rowBound * columnBound * ‖field‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2] using
      finiteAction_sum_sq_le coefficients majorant rowBound columnBound rowNonnegative
        columnNonnegative majorantNonnegative domination rows columns field
  have bound := Real.le_sqrt_of_sq_le squareBound
  rw [Real.sqrt_mul (mul_nonneg rowNonnegative columnNonnegative),
    Real.sqrt_sq (norm_nonneg field)] at bound
  exact bound

def finiteActionLinear (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut) :
    PiLp 2 (fun _ : Input => ValueIn) →ₗ[ℂ] PiLp 2 (fun _ : Output => ValueOut) where
  toFun := finiteAction coefficients
  map_add' first second := by
    apply PiLp.ext
    intro output
    change (∑ input, coefficients output input (first input + second input)) =
      (∑ input, coefficients output input (first input)) +
        ∑ input, coefficients output input (second input)
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' scalar field := by
    apply PiLp.ext
    intro output
    change (∑ input, coefficients output input (scalar • field input)) =
      scalar • ∑ input, coefficients output input (field input)
    simp only [map_smul, Finset.smul_sum]

omit [Fintype Output] in
theorem finiteActionLinear_apply (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (field : PiLp 2 (fun _ : Input => ValueIn)) :
    finiteActionLinear coefficients field = finiteAction coefficients field := rfl

section Bounds

variable (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
  (majorant : Output → Input → ℝ) (rowBound columnBound : ℝ)
  (rowNonnegative : 0 ≤ rowBound) (columnNonnegative : 0 ≤ columnBound)
  (majorantNonnegative : ∀ output input, 0 ≤ majorant output input)
  (domination : ∀ output input, ‖coefficients output input‖ ≤ majorant output input)
  (rows : ∀ output, ∑ input, majorant output input ≤ rowBound)
  (columns : ∀ input, ∑ output, majorant output input ≤ columnBound)

def finiteActionCLM : PiLp 2 (fun _ : Input => ValueIn) →L[ℂ]
    PiLp 2 (fun _ : Output => ValueOut) :=
  (finiteActionLinear coefficients).mkContinuous (Real.sqrt (rowBound * columnBound))
    (finiteAction_norm_le coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rows columns)

theorem finiteActionCLM_apply (field : PiLp 2 (fun _ : Input => ValueIn)) :
    finiteActionCLM coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rows columns field =
        finiteAction coefficients field := rfl

theorem finiteActionCLM_apply_coordinate (field : PiLp 2 (fun _ : Input => ValueIn))
    (output : Output) :
    finiteActionCLM coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rows columns field output =
        ∑ input, coefficients output input (field input) := rfl

theorem norm_finiteActionCLM :
    ‖finiteActionCLM coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rows columns‖ ≤
        Real.sqrt (rowBound * columnBound) :=
  (finiteActionLinear coefficients).mkContinuous_norm_le
    (Real.sqrt_nonneg (rowBound * columnBound))
    (finiteAction_norm_le coefficients majorant rowBound columnBound rowNonnegative
      columnNonnegative majorantNonnegative domination rows columns)

end Bounds
end Generic
end Grad.SchurKernel.Finite
