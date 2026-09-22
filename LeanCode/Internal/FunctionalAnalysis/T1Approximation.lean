import T1Averages

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open scoped Topology

universe valueUniverse

namespace Grad.SpatialTranslation

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem error_integrand_integrable (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (field : PlaneL2 Value) :
    Integrable (fun offset : Spatial => kernel offset • (translation Value offset field - field)) volume := by
  apply ((kernel_integrand_integrable Value kernel integrable field).sub
    (integrable.smul_const field)).congr
  exact Filter.Eventually.of_forall fun offset => (smul_sub (kernel offset) _ _).symm

theorem error_norm_ae (kernel : Spatial → ℝ)
    (nonnegative : ∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset) (field : PlaneL2 Value) :
    (fun offset : Spatial => ‖kernel offset • (translation Value offset field - field)‖) =ᵐ[volume]
      fun offset : Spatial => kernel offset * ‖translation Value offset field - field‖ := by
  filter_upwards [nonnegative] with offset positive
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg positive]

variable [CompleteSpace Value]

theorem average_sub_eq_integral (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (mass : (∫ offset, kernel offset) = 1) (field : PlaneL2 Value) :
    average Value kernel field - field =
      ∫ offset : Spatial, kernel offset • (translation Value offset field - field) := by
  rw [show (fun offset : Spatial => kernel offset • (translation Value offset field - field)) =
    (fun offset : Spatial => kernel offset • translation Value offset field - kernel offset • field) by
      funext offset; exact smul_sub _ _ _]
  rw [integral_sub (kernel_integrand_integrable Value kernel integrable field)
    (integrable.smul_const field), integral_smul_const, mass, one_smul]
  rfl

theorem average_error (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (nonnegative : ∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset)
    (mass : (∫ offset, kernel offset) = 1) (field : PlaneL2 Value) :
    Integrable (fun offset : Spatial => kernel offset * ‖translation Value offset field - field‖) volume ∧
    ‖average Value kernel field - field‖ ≤
      ∫ offset : Spatial, kernel offset * ‖translation Value offset field - field‖ := by
  refine ⟨(error_integrand_integrable Value kernel integrable field).norm.congr
    (error_norm_ae Value kernel nonnegative field), ?_⟩
  rw [average_sub_eq_integral Value kernel integrable mass field]
  exact (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (error_norm_ae Value kernel nonnegative field))

theorem average_smallSupport (field : PlaneL2 Value) (tolerance : ℝ) (positive : 0 < tolerance) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ kernel : Spatial → ℝ, Integrable kernel volume →
        (∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset) → (∫ offset, kernel offset) = 1 →
        (∀ᵐ offset ∂(volume : Measure Spatial), kernel offset ≠ 0 → ‖offset‖ < radius) →
        ‖average Value kernel field - field‖ < tolerance := by
  have continuous : ContinuousAt (fun offset : Spatial => translation Value offset field) 0 :=
    (translation_continuous Value field).continuousAt
  obtain ⟨radius, radiusPositive, nearby⟩ := Metric.continuousAt_iff.mp continuous
    (tolerance / 2) (half_pos positive)
  have nearbyNorm (offset : Spatial) (bound : ‖offset‖ < radius) :
      ‖translation Value offset field - field‖ < tolerance / 2 := by
    simpa only [translation_zero, dist_eq_norm, sub_zero] using nearby (by simpa using bound)
  refine ⟨radius, radiusPositive, ?_⟩
  intro kernel integrable nonnegative mass supported
  have error := average_error Value kernel integrable nonnegative mass field
  calc
    ‖average Value kernel field - field‖ ≤
        ∫ offset : Spatial, kernel offset * ‖translation Value offset field - field‖ := error.2
    _ ≤ ∫ offset : Spatial, kernel offset * (tolerance / 2) := by
      apply integral_mono_ae error.1 (integrable.mul_const (tolerance / 2))
      filter_upwards [nonnegative, supported] with offset positiveKernel support
      by_cases zero : kernel offset = 0
      · simp only [zero, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (nearbyNorm offset (support zero)).le positiveKernel
    _ = tolerance / 2 := by rw [integral_mul_const, mass, one_mul]
    _ < tolerance := half_lt_self positive

theorem error : ErrorGoal.{valueUniverse} := by
  intro Value normed inner complete kernel integrable nonnegative mass
  exact average_error Value kernel integrable nonnegative mass

theorem smallSupport : SmallSupportGoal.{valueUniverse} := by
  intro Value normed inner complete
  exact average_smallSupport Value

end Grad.SpatialTranslation
