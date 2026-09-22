import AJF30AugmentedCoordinateBudget
import AJF27SameSharedKnownHighResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit

section Fixed
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℝ (F context)]
  {budget : Context → ℕ → ℝ}

theorem uniformCoordinateBound_precomposeReal
    {family : (context : Context) → OrbitParameter → E context →L[ℝ] F context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (input : (context : Context) → X context →L[ℝ] E context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (inputBound : ∀ context, ‖input context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => (family context tau).comp (input context)) := by
  apply bound.map_bound smooth
    (fun context => (ContinuousLinearMap.compL ℝ (X context) (E context) (F context)).flip (input context)) constant nonnegative
  intro context operator
  exact (ContinuousLinearMap.opNorm_comp_le operator (input context)).trans
    ((mul_le_mul_of_nonneg_left (inputBound context) (norm_nonneg operator)).trans_eq (mul_comm _ _))

theorem uniformCoordinateBound_postcomposeReal
    {family : (context : Context) → OrbitParameter → X context →L[ℝ] E context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (output : (context : Context) → E context →L[ℝ] F context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (outputBound : ∀ context, ‖output context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => (output context).comp (family context tau)) := by
  apply bound.map_bound smooth
    (fun context => (ContinuousLinearMap.compL ℝ (X context) (E context) (F context)) (output context)) constant nonnegative
  intro context operator
  exact (ContinuousLinearMap.opNorm_comp_le (output context) operator).trans
    (mul_le_mul_of_nonneg_right (outputBound context) (norm_nonneg operator))
end Fixed

section Restriction
variable {Context : Type*} {E F : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedSpace ℝ (E context)] [∀ context, IsScalarTower ℝ ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  [∀ context, NormedSpace ℝ (F context)] [∀ context, IsScalarTower ℝ ℂ (F context)]
  {budget : Context → ℕ → ℝ}

theorem uniformCoordinateBound_restrictScalars
    {family : (context : Context) → OrbitParameter → E context →L[ℂ] F context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context)) :
    UniformCoordinateBound budget (fun context tau => (family context tau).restrictScalars ℝ) := by
  apply bound.map_bound smooth
    (fun context => (ContinuousLinearMap.restrictScalarsIsometry ℂ (E context) (F context) ℝ ℝ).toContinuousLinearMap) 1 (by norm_num)
  intro context operator
  exact ((ContinuousLinearMap.restrictScalarsIsometry ℂ (E context) (F context) ℝ ℝ).norm_map operator).le.trans_eq (one_mul _).symm
end Restriction

section Pair
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℝ (F context)]
  {budget : Context → ℕ → ℝ}

private theorem realLeft_norm (context : Context) :
    ‖(WithLp.prodContinuousLinearEquiv 2 ℝ (E context) (F context)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (E context) (F context))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (value, (0 : F context)))
  change ‖WithLp.toLp 2 (value, (0 : F context))‖ ^ 2 = ‖value‖ ^ 2 + ‖(0 : F context)‖ ^ 2 at square
  change ‖WithLp.toLp 2 (value, (0 : F context))‖ ≤ 1 * ‖value‖
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at square
  nlinarith [norm_nonneg (WithLp.toLp 2 (value, (0 : F context))), norm_nonneg value]

private theorem realRight_norm (context : Context) :
    ‖(WithLp.prodContinuousLinearEquiv 2 ℝ (E context) (F context)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (E context) (F context))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((0 : E context), value))
  change ‖WithLp.toLp 2 ((0 : E context), value)‖ ^ 2 = ‖(0 : E context)‖ ^ 2 + ‖value‖ ^ 2 at square
  change ‖WithLp.toLp 2 ((0 : E context), value)‖ ≤ 1 * ‖value‖
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at square
  nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : E context), value)), norm_nonneg value]

theorem uniformCoordinateBound_pairReal
    {first : (context : Context) → OrbitParameter → X context →L[ℝ] E context}
    {second : (context : Context) → OrbitParameter → X context →L[ℝ] F context}
    (firstBound : UniformCoordinateBound budget first) (secondBound : UniformCoordinateBound budget second)
    (firstSmooth : ∀ context, ContDiff ℝ ∞ (first context))
    (secondSmooth : ∀ context, ContDiff ℝ ∞ (second context)) :
    UniformCoordinateBound budget (fun context tau => realHilbertOperatorPair (first context tau) (second context tau)) := by
  let left := fun context => (WithLp.prodContinuousLinearEquiv 2 ℝ (E context) (F context)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (E context) (F context))
  let right := fun context => (WithLp.prodContinuousLinearEquiv 2 ℝ (E context) (F context)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (E context) (F context))
  have firstEstimate := uniformCoordinateBound_postcomposeReal firstBound firstSmooth left 1 (by norm_num)
    (fun context => realLeft_norm (E := E) (F := F) context)
  have secondEstimate := uniformCoordinateBound_postcomposeReal secondBound secondSmooth right 1 (by norm_num)
    (fun context => realRight_norm (E := E) (F := F) context)
  have combined := firstEstimate.add secondEstimate
    (fun context => realOperatorComposition_contDiff _ _ contDiff_const (firstSmooth context))
    (fun context => realOperatorComposition_contDiff _ _ contDiff_const (secondSmooth context))
  have same (context : Context) (tau : OrbitParameter) :
      (left context).comp (first context tau) + (right context).comp (second context tau) =
      realHilbertOperatorPair (first context tau) (second context tau) := by
    apply ContinuousLinearMap.ext
    intro value
    change WithLp.toLp 2 ((first context tau value, 0) + (0, second context tau value)) = WithLp.toLp 2 (first context tau value, second context tau value)
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simpa only [same] using combined
end Pair

end Grad.AnnularHighGenerators
