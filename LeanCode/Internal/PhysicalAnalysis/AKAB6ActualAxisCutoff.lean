import AKAB4UniformWeightedShellError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.WeightedAxisRemoval
open Grad.CompactCutoff Grad.PDEBootstrap

/-- Use the explicit radial inner-product bump; an arbitrary chosen bump
need not commute with angular averages. -/
def axisBumpFunction : Spatial → ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace Spatial).toFun 2

theorem axisBumpFunction_smooth : ContDiff ℝ ∞ axisBumpFunction := by
  apply contDiff_iff_contDiffAt.mpr
  intro point
  have smooth := (ContDiffBumpBase.ofInnerProductSpace Spatial).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (2,point) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set Spatial) from ⟨by norm_num,mem_univ _⟩))
  exact smooth.comp point ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Spatial => (2 : ℝ)) point).prodMk contDiffAt_id)

theorem axisBumpFunction_support : tsupport axisBumpFunction = Metric.closedBall (0 : Spatial) 2 := by
  change closure (Function.support ((ContDiffBumpBase.ofInnerProductSpace Spatial).toFun 2)) = _
  rw [(ContDiffBumpBase.ofInnerProductSpace Spatial).support 2 (by norm_num),closure_ball (0 : Spatial) (by norm_num : (2 : ℝ) ≠ 0)]

def axisBump : Cutoff (Metric.closedBall (0 : Spatial) 0) (Metric.ball (0 : Spatial) 3) where
  toFun := axisBumpFunction
  smooth := axisBumpFunction_smooth
  compact := by rw [HasCompactSupport,axisBumpFunction_support]; exact isCompact_closedBall _ _
  nonnegative := fun point => ((ContDiffBumpBase.ofInnerProductSpace Spatial).mem_Icc 2 point).1
  atMostOne := fun point => ((ContDiffBumpBase.ofInnerProductSpace Spatial).mem_Icc 2 point).2
  supported := by rw [axisBumpFunction_support]; exact Metric.closedBall_subset_ball (by norm_num)
  near := by
    refine ⟨Metric.ball (0 : Spatial) 1,Metric.isOpen_ball,Metric.closedBall_subset_ball (by norm_num),
      Metric.ball_subset_ball (by norm_num),?_⟩
    intro point inside
    exact (ContDiffBumpBase.ofInnerProductSpace Spatial).eq_one 2 (by norm_num) point
      (show ‖point‖ ≤ 1 from (show ‖point‖ < 1 from by simpa only [Metric.mem_ball,dist_zero_right] using inside).le)

def axisCutoff (epsilon : ℝ) (point : Spatial) : ℝ :=
  1 - axisBump.toFun (epsilon⁻¹ • point)

theorem axisCutoff_smooth (epsilon : ℝ) : ContDiff ℝ ∞ (axisCutoff epsilon) :=
  contDiff_const.sub (axisBump.smooth.comp (show ContDiff ℝ ∞ (fun point : Spatial => epsilon⁻¹ • point) from contDiff_id.const_smul epsilon⁻¹))

theorem axisCutoff_nonnegative (epsilon : ℝ) (point : Spatial) : 0 ≤ axisCutoff epsilon point :=
  sub_nonneg.mpr (axisBump.atMostOne _)

theorem axisCutoff_le_one (epsilon : ℝ) (point : Spatial) : axisCutoff epsilon point ≤ 1 := by
  dsimp [axisCutoff]
  exact sub_le_self _ (axisBump.nonnegative _)

theorem axisCutoff_zero (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (inside : ‖point‖ ≤ epsilon) : axisCutoff epsilon point = 0 := by
  have normBound : ‖epsilon⁻¹ • point‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
    calc
      _ ≤ epsilon⁻¹ * epsilon := mul_le_mul_of_nonneg_left inside (inv_nonneg.mpr positive.le)
      _ = 1 := inv_mul_cancel₀ positive.ne'
  have value := (ContDiffBumpBase.ofInnerProductSpace Spatial).eq_one 2 (by norm_num) (epsilon⁻¹ • point) normBound
  change 1 - (ContDiffBumpBase.ofInnerProductSpace Spatial).toFun 2 (epsilon⁻¹ • point) = 0
  rw [value,sub_self]

theorem axisCutoff_one (epsilon : ℝ) (positive : 0 < epsilon)
    (point : Spatial) (outside : 2 * epsilon ≤ ‖point‖) : axisCutoff epsilon point = 1 := by
  have normBound : 2 ≤ ‖epsilon⁻¹ • point‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
    calc
      2 = epsilon⁻¹ * (2 * epsilon) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left outside (inv_nonneg.mpr positive.le)
  have value : Real.smoothTransition ((2 - ‖epsilon⁻¹ • point‖) / (2 - 1)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  change 1 - Real.smoothTransition ((2 - ‖epsilon⁻¹ • point‖) / (2 - 1)) = 1
  rw [value,sub_zero]

theorem axisCutoff_fderiv (epsilon : ℝ) (point : Spatial) :
    fderiv ℝ (axisCutoff epsilon) point =
      -(fderiv ℝ axisBump.toFun (epsilon⁻¹ • point)).comp
        (epsilon⁻¹ • ContinuousLinearMap.id ℝ Spatial) := by
  have inner := (hasFDerivAt_id (𝕜 := ℝ) point).const_smul epsilon⁻¹
  have outer := (axisBump.smooth.differentiable (by simp) (epsilon⁻¹ • point)).hasFDerivAt
  have actual := ((hasFDerivAt_const (1 : ℝ) point).sub (outer.comp point inner)).fderiv
  have same : ((fun _ : Spatial => (1 : ℝ)) - axisBump.toFun ∘ (fun point : Spatial => epsilon⁻¹ • point)) =
      axisCutoff epsilon := by
    funext point
    rfl
  rw [same] at actual
  simpa only [zero_sub] using actual

theorem axisBump_derivative_bounded : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ point : Spatial, ‖fderiv ℝ axisBump.toFun point‖ ≤ constant := by
  obtain ⟨constant,bound⟩ := (axisBump.compact.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (axisBump.smooth.continuous_fderiv (by simp))
  exact ⟨max constant 0,le_max_right _ _,fun point => (bound point).trans (le_max_left _ _)⟩

def axisCutoffDerivativeConstant : ℝ := axisBump_derivative_bounded.choose

theorem axisCutoffDerivativeConstant_nonnegative : 0 ≤ axisCutoffDerivativeConstant :=
  axisBump_derivative_bounded.choose_spec.1

theorem axisCutoff_fderiv_bound (epsilon : ℝ) (positive : 0 < epsilon) (point : Spatial) :
    ‖fderiv ℝ (axisCutoff epsilon) point‖ ≤ axisCutoffDerivativeConstant / epsilon := by
  rw [axisCutoff_fderiv,norm_neg]
  have identity : ‖epsilon⁻¹ • ContinuousLinearMap.id ℝ Spatial‖ = epsilon⁻¹ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le),ContinuousLinearMap.norm_id,mul_one]
  calc
    _ ≤ ‖fderiv ℝ axisBump.toFun (epsilon⁻¹ • point)‖ * ‖epsilon⁻¹ • ContinuousLinearMap.id ℝ Spatial‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ axisCutoffDerivativeConstant / epsilon := by
      rw [identity,div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (axisBump_derivative_bounded.choose_spec.2 _) (inv_nonneg.mpr positive.le)

end Grad.WeightedAxisRemoval
