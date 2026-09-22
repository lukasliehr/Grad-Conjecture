import AKAB6ActualAxisCutoff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.WeightedAxisRemoval
open Grad.PDEBootstrap

theorem axisCutoff_germ_one (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (outside : 2 * epsilon < ‖point‖) :
    axisCutoff epsilon =ᶠ[𝓝 point] (fun _ => 1) := by
  have neighborhood : ∀ᶠ other : Spatial in 𝓝 point, 2 * epsilon < ‖other‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds outside
  exact neighborhood.mono (fun other bound => axisCutoff_one epsilon positive other bound.le)

theorem axisCutoff_germ_zero (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (inside : ‖point‖ < epsilon) :
    axisCutoff epsilon =ᶠ[𝓝 point] (fun _ => 0) := by
  have neighborhood : ∀ᶠ other : Spatial in 𝓝 point, ‖other‖ < epsilon :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds inside
  exact neighborhood.mono (fun other bound => axisCutoff_zero epsilon positive other bound.le)

theorem axisCutoff_fderiv_zero_outside (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (outside : 2 * epsilon < ‖point‖) :
    fderiv ℝ (axisCutoff epsilon) point = 0 := by
  rw [(axisCutoff_germ_one epsilon positive point outside).fderiv_eq]
  exact fderiv_const_apply (1 : ℝ)

/-- A single integrable dominator suffices for all shrinking cutoffs. -/
theorem axisCutoff_fderiv_radius_bound (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (nonzero : point ≠ 0) :
    ‖fderiv ℝ (axisCutoff epsilon) point‖ ≤ (2 * axisCutoffDerivativeConstant) / ‖point‖ := by
  have radiusPositive : 0 < ‖point‖ := norm_pos_iff.mpr nonzero
  by_cases outside : 2 * epsilon < ‖point‖
  · rw [axisCutoff_fderiv_zero_outside epsilon positive point outside,norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) axisCutoffDerivativeConstant_nonnegative) radiusPositive.le
  · apply (axisCutoff_fderiv_bound epsilon positive point).trans
    apply (div_le_div_iff₀ positive radiusPositive).mpr
    have bound := mul_le_mul_of_nonneg_left (le_of_not_gt outside) axisCutoffDerivativeConstant_nonnegative
    nlinarith only [bound]

theorem axisCutoff_eventually_one (epsilon : ℕ → ℝ) (positive : ∀ index, 0 < epsilon index)
    (vanishing : Tendsto epsilon atTop (𝓝 0)) (point : Spatial) (nonzero : point ≠ 0) :
    ∀ᶠ index in atTop, axisCutoff (epsilon index) point = 1 ∧
      fderiv ℝ (axisCutoff (epsilon index)) point = 0 := by
  have eventual : ∀ᶠ index in atTop, epsilon index < ‖point‖ / 2 :=
    vanishing.eventually (gt_mem_nhds (half_pos (norm_pos_iff.mpr nonzero)))
  filter_upwards [eventual] with index bound
  have outside : 2 * epsilon index < ‖point‖ := by linarith
  exact ⟨axisCutoff_one _ (positive index) point outside.le,
    axisCutoff_fderiv_zero_outside _ (positive index) point outside⟩

end Grad.WeightedAxisRemoval
