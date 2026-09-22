import AJD30UniformOperatorOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit

section Real
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℝ (F context)]
  {budget : Context → ℕ → ℝ}

theorem UniformCoordinateBound.composeReal
    {outer : (context : Context) → OrbitParameter → E context →L[ℝ] F context}
    {inner : (context : Context) → OrbitParameter → X context →L[ℝ] E context}
    (outerBound : UniformCoordinateBound budget outer) (innerBound : UniformCoordinateBound budget inner)
    (outerSmooth : ∀ context, ContDiff ℝ ∞ (outer context)) (innerSmooth : ∀ context, ContDiff ℝ ∞ (inner context))
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order)
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b)) :
    UniformCoordinateBound budget (fun context tau => (outer context tau).comp (inner context tau)) :=
  outerBound.bilinear innerBound outerSmooth innerSmooth
    (fun context => ContinuousLinearMap.compL ℝ (X context) (E context) (F context)) 1 (by norm_num)
    (fun context => ContinuousLinearMap.norm_compL_le ℝ (X context) (E context) (F context))
    budgetNonnegative pair pairNonnegative paired
end Real

section Complex
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  {budget : Context → ℕ → ℝ}

theorem UniformCoordinateBound.composeComplex
    {outer : (context : Context) → OrbitParameter → E context →L[ℂ] F context}
    {inner : (context : Context) → OrbitParameter → X context →L[ℂ] E context}
    (outerBound : UniformCoordinateBound budget outer) (innerBound : UniformCoordinateBound budget inner)
    (outerSmooth : ∀ context, ContDiff ℝ ∞ (outer context)) (innerSmooth : ∀ context, ContDiff ℝ ∞ (inner context))
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order)
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b)) :
    UniformCoordinateBound budget (fun context tau => (outer context tau).comp (inner context tau)) := by
  apply outerBound.bilinear innerBound outerSmooth innerSmooth
    (fun context => (ContinuousLinearMap.compL ℂ (X context) (E context) (F context)).bilinearRestrictScalars ℝ) 1 (by norm_num) _
    budgetNonnegative pair pairNonnegative paired
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro outerOperator
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro innerOperator
  change ‖outerOperator.comp innerOperator‖ ≤ (1 * ‖outerOperator‖) * ‖innerOperator‖
  simpa only [one_mul] using ContinuousLinearMap.opNorm_comp_le outerOperator innerOperator
end Complex
end Grad.AnnularCrossOrbit
