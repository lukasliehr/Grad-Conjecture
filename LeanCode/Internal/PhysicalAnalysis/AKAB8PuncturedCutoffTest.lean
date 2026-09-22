import AKAB7AxisCutoffLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.WeightedAxisRemoval
open Grad.PDEBootstrap Grad.WeakTesting

theorem axisCutoff_same_norm (epsilon : ℝ) (first second : Spatial) (same : ‖first‖ = ‖second‖) :
    axisCutoff epsilon first = axisCutoff epsilon second := by
  change 1 - Real.smoothTransition ((2 - ‖epsilon⁻¹ • first‖) / (2 - 1)) =
    1 - Real.smoothTransition ((2 - ‖epsilon⁻¹ • second‖) / (2 - 1))
  rw [norm_smul,norm_smul,same]

def axisCutoffTest (epsilon : ℝ) (test : Spatial → ℝ) (point : Spatial) : ℝ :=
  axisCutoff epsilon point * test point

theorem axisCutoffTest_smooth (epsilon : ℝ) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (axisCutoffTest epsilon test) :=
  (axisCutoff_smooth epsilon).mul smooth

theorem axisCutoffTest_compact (epsilon : ℝ) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) : HasCompactSupport (axisCutoffTest epsilon test) :=
  compact.mul_left

theorem axisCutoffTest_support (epsilon : ℝ) (test : Spatial → ℝ) :
    tsupport (axisCutoffTest epsilon test) ⊆ tsupport test := tsupport_mul_subset_right

theorem axisCutoffTest_away (epsilon : ℝ) (positive : 0 < epsilon) (test : Spatial → ℝ) :
    (0 : Spatial) ∉ tsupport (axisCutoffTest epsilon test) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have germ := axisCutoff_germ_zero epsilon positive (0 : Spatial) (by simpa using positive)
  filter_upwards [germ] with point same
  change axisCutoff epsilon point * test point = 0
  rw [same,zero_mul]

theorem orderedFirstTestDerivative (word : Fin 1 → Fin 2) (test : Spatial → ℝ) (point : Spatial) :
    orderedTestDerivative 1 word test point = fderiv ℝ test point (spatialDirection (word 0)) := by
  change iteratedFDeriv ℝ 1 test point (fun position => spatialDirection (word position)) = _
  exact iteratedFDeriv_one_apply (fun position => spatialDirection (word position))

theorem axisCutoffTest_fderiv (epsilon : ℝ) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (point direction : Spatial) :
    fderiv ℝ (axisCutoffTest epsilon test) point direction =
      axisCutoff epsilon point * fderiv ℝ test point direction +
        test point * fderiv ℝ (axisCutoff epsilon) point direction := by
  have product := fderiv_mul
    ((axisCutoff_smooth epsilon).differentiable (by simp) point)
    (smooth.differentiable (by simp) point)
  have same : axisCutoffTest epsilon test = axisCutoff epsilon * test := by funext point; rfl
  rw [same,product,add_apply,smul_apply,smul_apply]
  simp only [smul_eq_mul]

end Grad.WeightedAxisRemoval
