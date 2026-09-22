import AKAL2ActualUniformCoefficientBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Grad.CartesianStartup

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem startupComposition_norm (outer : F →L[ℂ] G) (inner : E →L[ℂ] F)
    {a b : ℝ} (outerBound : ‖outer‖ ≤ a) (innerBound : ‖inner‖ ≤ b) :
    ‖outer.comp inner‖ ≤ a * b :=
  (outer.opNorm_comp_le inner).trans (mul_le_mul outerBound innerBound (norm_nonneg _) ((norm_nonneg _).trans outerBound))

theorem startupCurrent_norm (extension complement gauge : E →L[ℂ] E)
    {e k g : ℝ} (eBound : ‖extension‖ ≤ e) (kBound : ‖complement‖ ≤ k) (gBound : ‖gauge‖ ≤ g) :
    ‖ContinuousLinearMap.id ℂ E - extension.comp (complement.comp gauge)‖ ≤ 1 + e * (k * g) := by
  exact (norm_sub_le _ _).trans
    (add_le_add (ContinuousLinearMap.norm_id_le) (startupComposition_norm extension _ eBound
      (startupComposition_norm complement gauge kBound gBound)))

theorem startupTwiceComposition_norm (outer : F →L[ℂ] G) (middle : E →L[ℂ] F)
    (inner : H →L[ℂ] E) {k a q : ℝ}
    (outerBound : ‖outer‖ ≤ k) (middleBound : ‖middle‖ ≤ a) (innerBound : ‖inner‖ ≤ q) :
    ‖(2 : ℂ) • outer.comp (middle.comp inner)‖ ≤ 2 * (k * (a * q)) := by
  rw [norm_smul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left
    (startupComposition_norm outer _ outerBound (startupComposition_norm middle inner middleBound innerBound)) (by norm_num)

theorem startupHalfComposition_norm (outer : F →L[ℂ] G) (middle : E →L[ℂ] F)
    (inner : H →L[ℂ] E) {k a q : ℝ}
    (outerBound : ‖outer‖ ≤ k) (middleBound : ‖middle‖ ≤ a) (innerBound : ‖inner‖ ≤ q) :
    ‖(1 / 2 : ℂ) • outer.comp (middle.comp inner)‖ ≤ k * (a * q) := by
  have bound := startupComposition_norm outer _ outerBound (startupComposition_norm middle inner middleBound innerBound)
  rw [norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have n := norm_nonneg (outer.comp (middle.comp inner))
  linarith

end Grad.CartesianStartup
