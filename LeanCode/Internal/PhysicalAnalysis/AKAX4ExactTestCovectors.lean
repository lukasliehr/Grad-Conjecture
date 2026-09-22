import AKAX3ActualAngularTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct

/-- Expand a genuine scalar derivative in the fixed Cartesian directions. -/
theorem startupDerivative_coordinates (derivative : Spatial →L[ℝ] ℝ) (direction : Spatial) :
    derivative direction = ∑ coordinate : Fin 2, direction coordinate * derivative (spatialDirection coordinate) := by
  calc
    derivative direction = derivative (∑ coordinate : Fin 2, direction coordinate • spatialDirection coordinate) :=
      congrArg derivative (Grad.OrthogonalCoefficients.Composition.spatialDirection_expansion direction)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

theorem startupRotatedTest_derivative (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (scalar : ℝ)
    (point : Spatial) (direction : Fin 2) :
    fderiv ℝ (fun source => scalar * test (orthogonal source)) point (spatialDirection direction) =
      ∑ coordinate : Fin 2, (scalar * orthogonal (spatialDirection direction) coordinate) *
        fderiv ℝ test (orthogonal point) (spatialDirection coordinate) := by
  have derivative := ((smooth.differentiable (by simp) (orthogonal point)).hasFDerivAt.comp point
    orthogonal.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).const_mul scalar
  simp only [Function.comp_def] at derivative
  rw [derivative.fderiv]
  change scalar * fderiv ℝ test (orthogonal point) (orthogonal (spatialDirection direction)) = _
  rw [startupDerivative_coordinates, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Differentiate under the actual compact angular integral, keeping the literal inverse covector. -/
theorem startupAngularTest_derivative_integral (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) (direction : Fin 2) :
    fderiv ℝ (startupAngularTest weight test) point (spatialDirection direction) =
      (2 * Real.pi)⁻¹ * ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        ∑ coordinate : Fin 2, (weight angle * startupInverseRotationEntry direction coordinate angle) *
          fderiv ℝ test (planeRotationEquiv (-angle) point) (spatialDirection coordinate) := by
  let integrand : Spatial × ℝ → ℝ := fun argument =>
    weight argument.2 * test (planeRotationEquiv (-argument.2) argument.1)
  have smooth : ContDiff ℝ ∞ integrand :=
    (weightSmooth.comp contDiff_snd).mul (testSmooth.comp startupInverseTestRotation_smooth)
  have derivative := (hasFDerivAt_compactIntegral isOpen_univ smooth.contDiffOn 0 (2 * Real.pi)
    point (mem_univ point)).const_mul ((2 * Real.pi)⁻¹ : ℝ)
  change fderiv ℝ (fun source => (2 * Real.pi)⁻¹ * ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    integrand (source, angle)) point (spatialDirection direction) = _
  rw [derivative.fderiv]
  change (2 * Real.pi)⁻¹ * (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    integralParameterDerivative integrand (point, angle)) (spatialDirection direction) = _
  have partialContinuous : Continuous (fun angle => integralParameterDerivative integrand (point, angle)) :=
    (integralParameterDerivative_smooth (domain := (univ : Set Spatial)) isOpen_univ smooth.contDiffOn).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨mem_univ _, mem_univ _⟩)
  rw [ContinuousLinearMap.integral_apply partialContinuous.integrableOn_Icc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [integralParameterDerivative_eq point angle (smooth.differentiable (by simp) (point, angle))]
  exact startupRotatedTest_derivative (planeRotationEquiv (-angle)) test testSmooth (weight angle) point direction

end Grad.CartesianStartup
