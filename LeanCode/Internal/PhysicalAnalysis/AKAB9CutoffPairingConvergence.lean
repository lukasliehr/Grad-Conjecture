import AKAB8PuncturedCutoffTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.WeightedAxisRemoval
open Grad.PDEBootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure Spatial) (away : ∀ᵐ point ∂measure, point ≠ 0)
    (epsilon : ℕ → ℝ) (positive : ∀ index, 0 < epsilon index)
    (vanishing : Tendsto epsilon atTop (𝓝 0))

include away positive vanishing

theorem axisCutoff_integral_tendsto (field : Spatial → E) (integrable : Integrable field measure) :
    Tendsto (fun index => ∫ point, axisCutoff (epsilon index) point • field point ∂measure)
      atTop (𝓝 (∫ point, field point ∂measure)) := by
  apply tendsto_integral_of_dominated_convergence (fun point => ‖field point‖)
  · intro index
    exact (axisCutoff_smooth (epsilon index)).continuous.aestronglyMeasurable.smul integrable.aestronglyMeasurable
  · exact integrable.norm
  · intro index
    filter_upwards with point
    rw [norm_smul,Real.norm_of_nonneg (axisCutoff_nonnegative _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (axisCutoff_le_one _ _)
  · filter_upwards [away] with point nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [axisCutoff_eventually_one epsilon positive vanishing point nonzero] with index same
    simp only [same.1,one_smul]

theorem axisCutoff_derivative_integral_tendsto (field : Spatial → E)
    (measurable : AEStronglyMeasurable field measure)
    (weightedIntegrable : Integrable (fun point => ‖point‖⁻¹ * ‖field point‖) measure)
    (direction : Spatial) :
    Tendsto (fun index => ∫ point,
      (fderiv ℝ (axisCutoff (epsilon index)) point direction) • field point ∂measure) atTop (𝓝 0) := by
  have convergence := tendsto_integral_of_dominated_convergence
    (μ := measure) (f := fun _ : Spatial => (0 : E))
    (fun point => (2 * axisCutoffDerivativeConstant * ‖direction‖) * (‖point‖⁻¹ * ‖field point‖))
    (F := fun index point => (fderiv ℝ (axisCutoff (epsilon index)) point direction) • field point)
    (fun index => (((axisCutoff_smooth (epsilon index)).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.smul measurable)
    (weightedIntegrable.const_mul _) (fun index => ?_) ?_
  · simpa only [integral_zero] using convergence
  · filter_upwards [away] with point nonzero
    rw [norm_smul]
    have derivative := ((fderiv ℝ (axisCutoff (epsilon index)) point).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right (axisCutoff_fderiv_radius_bound _ (positive index) point nonzero) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_right derivative (norm_nonneg _)).trans_eq (by rw [div_eq_mul_inv]; ring)
  · filter_upwards [away] with point nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [axisCutoff_eventually_one epsilon positive vanishing point nonzero] with index same
    simp only [same.2,zero_apply,zero_smul]

end Grad.WeightedAxisRemoval
