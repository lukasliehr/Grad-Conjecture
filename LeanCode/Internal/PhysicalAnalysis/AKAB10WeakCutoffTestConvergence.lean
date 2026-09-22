import AKAB9CutoffPairingConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.WeightedAxisRemoval
open Grad.PDEBootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure Spatial) (away : ∀ᵐ point ∂measure, point ≠ 0)
    (epsilon : ℕ → ℝ) (positive : ∀ index, 0 < epsilon index)
    (vanishing : Tendsto epsilon atTop (𝓝 0))

theorem compactTest_smul_integrable (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (field : Spatial → E) (integrable : Integrable field measure) :
    Integrable (fun point => test point • field point) measure := by
  obtain ⟨constant,bound⟩ := compact.exists_bound_of_continuous smooth.continuous
  exact integrable.bdd_smul constant smooth.continuous.aestronglyMeasurable (Eventually.of_forall bound)

include away positive vanishing

theorem axisCutoffTest_integral_tendsto (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (field : Spatial → E) (integrable : Integrable field measure) :
    Tendsto (fun index => ∫ point, axisCutoffTest (epsilon index) test point • field point ∂measure)
      atTop (𝓝 (∫ point, test point • field point ∂measure)) := by
  have convergence := axisCutoff_integral_tendsto measure away epsilon positive vanishing
    (fun point => test point • field point) (compactTest_smul_integrable measure test smooth compact field integrable)
  simpa only [axisCutoffTest,mul_smul] using convergence

theorem axisCutoffTest_derivative_integral_tendsto (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (field : Spatial → E) (integrable : Integrable field measure)
    (weightedIntegrable : Integrable (fun point => ‖point‖⁻¹ * ‖field point‖) measure)
    (direction : Spatial) :
    Tendsto (fun index => ∫ point,
      (fderiv ℝ (axisCutoffTest (epsilon index) test) point direction) • field point ∂measure)
      atTop (𝓝 (∫ point, (fderiv ℝ test point direction) • field point ∂measure)) := by
  obtain ⟨rawValue,valueBound⟩ := compact.exists_bound_of_continuous smooth.continuous
  obtain ⟨rawDerivative,derivativeBound⟩ := (compact.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (smooth.continuous_fderiv (by simp))
  let C0 := max rawValue 0
  let C1 := max rawDerivative 0
  have C0nonnegative : 0 ≤ C0 := le_max_right _ _
  have C1nonnegative : 0 ≤ C1 := le_max_right _ _
  have C0bound (point : Spatial) : ‖test point‖ ≤ C0 := (valueBound point).trans (le_max_left _ _)
  have C1bound (point : Spatial) : ‖fderiv ℝ test point‖ ≤ C1 := (derivativeBound point).trans (le_max_left _ _)
  apply tendsto_integral_of_dominated_convergence
    (fun point => (C1 * ‖direction‖) * ‖field point‖ +
      (C0 * (2 * axisCutoffDerivativeConstant) * ‖direction‖) * (‖point‖⁻¹ * ‖field point‖))
  · intro index
    exact (((axisCutoffTest_smooth (epsilon index) test smooth).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.smul integrable.aestronglyMeasurable
  · exact (integrable.norm.const_mul _).add (weightedIntegrable.const_mul _)
  · intro index
    filter_upwards [away] with point nonzero
    have original : ‖fderiv ℝ test point direction‖ ≤ C1 * ‖direction‖ :=
      ((fderiv ℝ test point).le_opNorm direction).trans (mul_le_mul_of_nonneg_right (C1bound point) (norm_nonneg _))
    have cutoff : ‖fderiv ℝ (axisCutoff (epsilon index)) point direction‖ ≤
        ((2 * axisCutoffDerivativeConstant) / ‖point‖) * ‖direction‖ :=
      ((fderiv ℝ (axisCutoff (epsilon index)) point).le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right (axisCutoff_fderiv_radius_bound _ (positive index) point nonzero) (norm_nonneg _))
    have cutoffValue : ‖axisCutoff (epsilon index) point‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (axisCutoff_nonnegative _ _)]
      exact axisCutoff_le_one _ _
    have derivative : ‖fderiv ℝ (axisCutoffTest (epsilon index) test) point direction‖ ≤
        C1 * ‖direction‖ + C0 * (((2 * axisCutoffDerivativeConstant) / ‖point‖) * ‖direction‖) := by
      rw [axisCutoffTest_fderiv _ test smooth]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      exact add_le_add
        ((mul_le_mul cutoffValue original (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
        (mul_le_mul (C0bound point) cutoff (norm_nonneg _) C0nonnegative)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right derivative (norm_nonneg _)).trans_eq (by rw [div_eq_mul_inv]; ring)
  · filter_upwards [away] with point nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [axisCutoff_eventually_one epsilon positive vanishing point nonzero] with index same
    rw [axisCutoffTest_fderiv _ test smooth,same.1,same.2,zero_apply,one_mul,mul_zero,add_zero]

end Grad.WeightedAxisRemoval
