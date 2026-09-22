import MP1Interface

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Function
open scoped ContDiff

namespace Grad.Mollifier.Pointwise

theorem rawBump_formula (point : Spatial) :
    rawBump point = Real.smoothTransition (2 - 2 * ‖point‖) := by
  norm_num [rawBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul]

theorem rawBump_nonneg (point : Spatial) : 0 ≤ rawBump point :=
  ((ContDiffBumpBase.ofInnerProductSpace Spatial).mem_Icc 2 ((2 : ℝ) • point)).1

theorem rawBump_contDiff : ContDiff ℝ ∞ rawBump := by
  have scaled : ContDiff ℝ ∞ (fun point : Spatial => (2 : ℝ) • point) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (2 : ℝ) : Spatial →L[ℝ] Spatial).contDiff
  have paired : ContDiff ℝ ∞ (fun point : Spatial => ((2 : ℝ), (2 : ℝ) • point)) :=
    contDiff_const.prodMk scaled
  exact (ContDiffBumpBase.ofInnerProductSpace Spatial).smooth.comp_contDiff
    paired (fun _point => ⟨by norm_num, Set.mem_univ _⟩)

theorem rawBump_support : support rawBump = Metric.ball (0 : Spatial) 1 := by
  ext point
  simp only [mem_support, rawBump_formula, ne_eq, Real.smoothTransition.zero_iff_nonpos,
    not_le, Metric.mem_ball, dist_zero_right]
  constructor <;> intro inequality <;> linarith

theorem rawBump_tsupport : tsupport rawBump = Metric.closedBall (0 : Spatial) 1 := by
  rw [tsupport, rawBump_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem rawBump_compactSupport : HasCompactSupport rawBump := by
  rw [HasCompactSupport, rawBump_tsupport]
  exact isCompact_closedBall (0 : Spatial) 1

theorem rawBump_integrable : Integrable rawBump volume :=
  rawBump_contDiff.continuous.integrable_of_hasCompactSupport rawBump_compactSupport

theorem rawBump_integral_pos : 0 < ∫ point : Spatial, rawBump point := by
  apply (integral_pos_iff_support_of_nonneg rawBump_nonneg rawBump_integrable).mpr
  rw [rawBump_support]
  exact Metric.measure_ball_pos volume (0 : Spatial) (by norm_num : (0 : ℝ) < 1)

theorem eta_nonneg (point : Spatial) : 0 ≤ eta point :=
  div_nonneg (rawBump_nonneg point) rawBump_integral_pos.le

theorem eta_contDiff : ContDiff ℝ ∞ eta := rawBump_contDiff.div_const _

theorem eta_support : support eta = Metric.ball (0 : Spatial) 1 := by
  unfold eta
  rw [support_div, rawBump_support, support_const rawBump_integral_pos.ne', Set.inter_univ]

theorem eta_tsupport : tsupport eta = Metric.closedBall (0 : Spatial) 1 := by
  rw [tsupport, eta_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem eta_compactSupport : HasCompactSupport eta := by
  rw [HasCompactSupport, eta_tsupport]
  exact isCompact_closedBall (0 : Spatial) 1

theorem eta_integrable : Integrable eta volume := rawBump_integrable.div_const _

theorem eta_integral : (∫ point : Spatial, eta point) = 1 := by
  unfold eta
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ rawBump_integral_pos.ne'

theorem eta_orthogonal (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) :
    eta (orthogonal point) = eta point := by
  simp only [eta, rawBump_formula, orthogonal.norm_map]

theorem bumpGoal : BumpGoal :=
  ⟨rawBump_formula, rawBump_integrable, rawBump_integral_pos, eta_nonneg, eta_contDiff,
    eta_compactSupport, eta_support, eta_tsupport, eta_integrable, eta_integral, eta_orthogonal⟩

theorem scaledEta_nonneg (epsilon : ℝ) (positive : 0 < epsilon) (point : Spatial) :
    0 ≤ scaledEta epsilon point :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg positive.le 2)) (eta_nonneg _)

theorem scaledEta_contDiff (epsilon : ℝ) : ContDiff ℝ ∞ (scaledEta epsilon) := by
  have composition : ContDiff ℝ ∞ (fun point : Spatial => eta (epsilon⁻¹ • point)) :=
    eta_contDiff.comp (ContinuousLinearMap.lsmul ℝ ℝ epsilon⁻¹ : Spatial →L[ℝ] Spatial).contDiff
  exact contDiff_const.mul composition

theorem scaledEta_support (epsilon : ℝ) (positive : 0 < epsilon) :
    support (scaledEta epsilon) = Metric.ball (0 : Spatial) epsilon := by
  have nonzero : (epsilon ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 positive.ne')
  have eta_nonzero (point : Spatial) : eta point ≠ 0 ↔ ‖point‖ < 1 := by
    change point ∈ support eta ↔ _
    rw [eta_support, Metric.mem_ball, dist_zero_right]
  ext point
  change (epsilon ^ 2)⁻¹ * eta (epsilon⁻¹ • point) ≠ 0 ↔ dist point 0 < epsilon
  rw [mul_ne_zero_iff, and_iff_right nonzero, eta_nonzero, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos positive, ← div_eq_inv_mul, div_lt_one positive]

theorem scaledEta_tsupport (epsilon : ℝ) (positive : 0 < epsilon) :
    tsupport (scaledEta epsilon) = Metric.closedBall (0 : Spatial) epsilon := by
  rw [tsupport, scaledEta_support epsilon positive, closure_ball _ positive.ne']

theorem scaledEta_compactSupport (epsilon : ℝ) (positive : 0 < epsilon) :
    HasCompactSupport (scaledEta epsilon) := by
  rw [HasCompactSupport, scaledEta_tsupport epsilon positive]
  exact isCompact_closedBall (0 : Spatial) epsilon

theorem scaledEta_integrable (epsilon : ℝ) (positive : 0 < epsilon) :
    Integrable (scaledEta epsilon) volume :=
  (scaledEta_contDiff epsilon).continuous.integrable_of_hasCompactSupport
    (scaledEta_compactSupport epsilon positive)

theorem scaledEta_integral (epsilon : ℝ) (positive : 0 < epsilon) :
    (∫ point : Spatial, scaledEta epsilon point) = 1 := by
  unfold scaledEta
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume eta epsilon]
  simp only [Spatial, finrank_euclideanSpace_fin, eta_integral, smul_eq_mul, mul_one,
    abs_of_nonneg (pow_nonneg positive.le 2)]
  exact inv_mul_cancel₀ (pow_ne_zero 2 positive.ne')

theorem scaledEta_kernelL1 (epsilon : ℝ) (positive : 0 < epsilon) :
    Grad.SpatialTranslation.kernelL1 (scaledEta epsilon) = 1 := by
  calc
    _ = ∫ point : Spatial, scaledEta epsilon point := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => abs_of_nonneg (scaledEta_nonneg epsilon positive point))
    _ = 1 := scaledEta_integral epsilon positive

theorem scaledEta_orthogonal (epsilon : ℝ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) :
    scaledEta epsilon (orthogonal point) = scaledEta epsilon point := by
  unfold scaledEta
  rw [← orthogonal.map_smul, eta_orthogonal]

theorem scalingGoal : ScalingGoal := by
  intro epsilon positive
  exact ⟨fun _point => rfl, scaledEta_nonneg epsilon positive, scaledEta_contDiff epsilon,
    scaledEta_compactSupport epsilon positive, scaledEta_support epsilon positive,
    scaledEta_tsupport epsilon positive, scaledEta_integrable epsilon positive,
    scaledEta_integral epsilon positive, scaledEta_kernelL1 epsilon positive, scaledEta_orthogonal epsilon⟩

end Grad.Mollifier.Pointwise
