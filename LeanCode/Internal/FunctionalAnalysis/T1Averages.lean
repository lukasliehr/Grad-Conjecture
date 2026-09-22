import T1Translation

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open scoped Topology ContDiff

universe valueUniverse

namespace Grad.SpatialTranslation

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem kernel_integrand_integrable (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (field : PlaneL2 Value) :
    Integrable (fun offset : Spatial => kernel offset • translation Value offset field) volume := by
  apply (integrable.abs.mul_const ‖field‖).mono'
  · exact integrable.aestronglyMeasurable.smul
      (translation_continuous Value field).stronglyMeasurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun offset => by
      simp only [norm_smul, Real.norm_eq_abs, translation_norm, le_refl]

theorem kernelL1_nonneg (kernel : Spatial → ℝ) : 0 ≤ kernelL1 kernel :=
  integral_nonneg fun offset => abs_nonneg (kernel offset)

variable [CompleteSpace Value]

theorem average_norm_le (kernel : Spatial → ℝ) (field : PlaneL2 Value) :
    ‖average Value kernel field‖ ≤ kernelL1 kernel * ‖field‖ := by
  calc
    ‖average Value kernel field‖ ≤ ∫ offset : Spatial, ‖kernel offset • translation Value offset field‖ :=
      norm_integral_le_integral_norm _
    _ = kernelL1 kernel * ‖field‖ := by
      simp only [norm_smul, Real.norm_eq_abs, translation_norm, integral_mul_const, kernelL1]

theorem average_add (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (first second : PlaneL2 Value) :
    average Value kernel (first + second) = average Value kernel first + average Value kernel second := by
  simp only [average, map_add, smul_add]
  exact integral_add (kernel_integrand_integrable Value kernel integrable first)
    (kernel_integrand_integrable Value kernel integrable second)

theorem average_smul (kernel : Spatial → ℝ) (scalar : ℂ) (field : PlaneL2 Value) :
    average Value kernel (scalar • field) = scalar • average Value kernel field := by
  simp only [average, map_smul, smul_comm (kernel _) scalar, integral_smul]

def averagingCLM (kernel : Spatial → ℝ) (integrable : Integrable kernel volume) :
    PlaneL2 Value →L[ℂ] PlaneL2 Value :=
  ({ toFun := average Value kernel
     map_add' := average_add Value kernel integrable
     map_smul' := average_smul Value kernel } : PlaneL2 Value →ₗ[ℂ] PlaneL2 Value).mkContinuous
    (kernelL1 kernel) (average_norm_le Value kernel)

theorem averagingCLM_apply (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (field : PlaneL2 Value) : averagingCLM Value kernel integrable field = average Value kernel field := rfl

theorem averagingCLM_norm_le (kernel : Spatial → ℝ) (integrable : Integrable kernel volume) :
    ‖averagingCLM Value kernel integrable‖ ≤ kernelL1 kernel :=
  ContinuousLinearMap.opNorm_le_bound _ (kernelL1_nonneg kernel) (average_norm_le Value kernel)

theorem functional_average (kernel : Spatial → ℝ) (integrable : Integrable kernel volume)
    (functional : PlaneL2 Value →L[ℂ] ℂ) (field : PlaneL2 Value) :
    Integrable (fun offset : Spatial => kernel offset • functional (translation Value offset field)) volume ∧
    functional (average Value kernel field) =
      ∫ offset : Spatial, kernel offset • functional (translation Value offset field) := by
  have integrand := kernel_integrand_integrable Value kernel integrable field
  constructor
  · simpa only [LinearMapClass.map_smul_of_tower functional] using functional.integrable_comp integrand
  · simpa only [average, LinearMapClass.map_smul_of_tower functional] using
      (functional.integral_comp_comm integrand).symm

theorem kernelL1_eq_one (kernel : Spatial → ℝ)
    (nonnegative : ∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset)
    (mass : (∫ offset, kernel offset) = 1) : kernelL1 kernel = 1 := by
  calc
    kernelL1 kernel = ∫ offset : Spatial, kernel offset :=
      integral_congr_ae (nonnegative.mono fun _ positive => abs_of_nonneg positive)
    _ = 1 := mass

theorem average_contraction (kernel : Spatial → ℝ)
    (nonnegative : ∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset)
    (mass : (∫ offset, kernel offset) = 1) (field : PlaneL2 Value) :
    ‖average Value kernel field‖ ≤ ‖field‖ := by
  simpa only [kernelL1_eq_one kernel nonnegative mass, one_mul] using average_norm_le Value kernel field

theorem averaging : AveragingGoal.{valueUniverse} := by
  intro Value normed inner complete kernel integrable
  exact ⟨kernel_integrand_integrable Value kernel integrable, average_norm_le Value kernel,
    average_add Value kernel integrable, average_smul Value kernel,
    ⟨averagingCLM Value kernel integrable, averagingCLM_apply Value kernel integrable,
      averagingCLM_norm_le Value kernel integrable⟩⟩

theorem functional : FunctionalGoal.{valueUniverse} := by
  intro Value normed inner complete kernel integrable
  exact functional_average Value kernel integrable

theorem contraction : ContractionGoal.{valueUniverse} := by
  intro Value normed inner complete kernel integrable nonnegative mass
  refine ⟨average_contraction Value kernel nonnegative mass, ?_⟩
  intro averaging applications
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [applications, one_mul] using average_contraction Value kernel nonnegative mass field

theorem compactPairing_translation (dimension : ℕ) (field : FieldL2 dimension Set.univ)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (offset : Spatial) :
    Grad.WeakTesting.compactPairing dimension Set.univ cell vector test smooth compact
        (translation (CellValues dimension) offset field) =
      ∫ point : Spatial, test point • inner ℂ vector (field (point - offset) cell) := by
  rw [Grad.WeakTesting.compactPairing_apply]
  change (∫ point in Set.univ, test point • inner ℂ vector
    (translation (CellValues dimension) offset field point cell)) = _
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [translation_ae (CellValues dimension) offset field] with point equality
  rw [equality]

theorem compactTest_translation_integrable (dimension : ℕ) (field : FieldL2 dimension Set.univ)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (offset : Spatial) :
    Integrable (fun point : Spatial => test point • inner ℂ vector (field (point - offset) cell)) volume := by
  have translated := Grad.WeakTesting.pairing_integrable dimension Set.univ cell vector test
    (smooth.continuous.memLp_of_hasCompactSupport compact)
    (translation (CellValues dimension) offset field)
  have full : Integrable (fun point : Spatial => test point • inner ℂ vector
      (translation (CellValues dimension) offset field point cell)) volume :=
    integrableOn_univ.mp translated
  apply full.congr
  filter_upwards [translation_ae (CellValues dimension) offset field] with point equality
  rw [equality]

theorem compactTest : CompactTestGoal := by
  intro dimension kernel integrable field cell vector test smooth compact
  simpa only [compactPairing_translation] using
    functional_average (CellValues dimension) kernel integrable
      (Grad.WeakTesting.compactPairing dimension Set.univ cell vector test smooth compact) field

end Grad.SpatialTranslation
