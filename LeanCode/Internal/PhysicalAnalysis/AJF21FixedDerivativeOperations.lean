import AJF18PositiveJetCompositionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace Grad.AnnularOrbitGenerators

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Fixed real maps commute with genuine one-variable derivatives. -/
theorem iteratedDeriv_fixedMap (mapping : E →L[ℝ] F) (function : ℝ → E)
    (smooth : ContDiff ℝ ∞ function) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter => mapping (function parameter)) time =
      mapping (iteratedDeriv order function time) := by
  have derivative := mapping.iteratedFDeriv_comp_left (x := time) smooth.contDiffAt
    (i := order) (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
  have actual := congrArg (fun multilinear : ContinuousMultilinearMap ℝ (fun _ : Fin order => ℝ) F =>
    multilinear (fun _ => 1)) derivative
  change (iteratedFDeriv ℝ order (fun parameter => mapping (function parameter)) time) (fun _ => 1) =
    mapping ((iteratedFDeriv ℝ order function time) (fun _ => 1)) at actual
  simpa only [← iteratedDeriv_eq_iteratedFDeriv] using actual

/-- A fixed incoming lift only contributes its original operator norm to
positive derivatives of the actual constant-minus-correction operator. -/
theorem iteratedDeriv_constantMinusComposition_bound (constant fixed : E →L[ℝ] F)
    (operator : ℝ → F →L[ℝ] F) (smooth : ContDiff ℝ ∞ operator)
    (order : ℕ) (positive : 0 < order) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => constant - (operator parameter).comp fixed) time‖ ≤
      ‖iteratedDeriv order operator time‖ * ‖fixed‖ := by
  rw [iteratedDeriv_const_sub positive, iteratedDeriv_neg, norm_neg]
  have actual := iteratedDeriv_fixedMap ((ContinuousLinearMap.compL ℝ E F F).flip fixed)
    operator smooth order time
  exact (congrArg norm actual).le.trans
    (ContinuousLinearMap.opNorm_comp_le _ _)

end Grad.AnnularOrbitGenerators
