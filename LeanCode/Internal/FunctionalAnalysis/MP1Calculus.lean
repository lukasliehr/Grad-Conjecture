import MP1Kernel

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff

namespace Grad.Mollifier.Pointwise

universe valueUniverse

variable {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem convolution_integrable (kernel : Spatial → ℝ) (function : Spatial → Value)
    (continuousKernel : Continuous kernel) (compactSupport : HasCompactSupport kernel)
    (integrableLocally : LocallyIntegrable function volume) (point : Spatial) :
    Integrable (fun source : Spatial => kernel (point - source) • function source) volume :=
  compactSupport.convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Value →L[ℝ] Value).flip integrableLocally continuousKernel point

theorem convolution_contDiff (kernel : Spatial → ℝ) (function : Spatial → Value)
    (smoothness : ContDiff ℝ ∞ kernel) (compactSupport : HasCompactSupport kernel)
    (integrableLocally : LocallyIntegrable function volume) : ContDiff ℝ ∞ (convolution kernel function) :=
  compactSupport.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Value →L[ℝ] Value).flip integrableLocally smoothness

theorem convolution_direction (kernel : Spatial → ℝ) (function : Spatial → Value)
    (smoothness : ContDiff ℝ ∞ kernel) (compactSupport : HasCompactSupport kernel)
    (integrableLocally : LocallyIntegrable function volume) (point direction : Spatial) :
    fderiv ℝ (convolution kernel function) point direction =
      convolution (fun source => fderiv ℝ kernel source direction) function point := by
  let multiplication : Value →L[ℝ] ℝ →L[ℝ] Value :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Value →L[ℝ] Value).flip
  change fderiv ℝ (MeasureTheory.convolution function kernel multiplication volume) point direction = _
  rw [(compactSupport.hasFDerivAt_convolution_right multiplication integrableLocally
    (smoothness.of_le (by simp)) point).fderiv]
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ kernel) := smoothness.fderiv_right (by simp)
  exact MeasureTheory.convolution_precompR_apply multiplication integrableLocally (compactSupport.fderiv ℝ)
    derivativeSmooth.continuous point direction

theorem orderedDerivative_convolution (kernel : Spatial → ℝ) (function : Spatial → Value)
    (smoothness : ContDiff ℝ ∞ kernel) (compactSupport : HasCompactSupport kernel)
    (integrableLocally : LocallyIntegrable function volume) (rank : ℕ) (word : Word rank) :
    orderedDerivative rank word (convolution kernel function) =
      convolution (orderedDerivative rank word kernel) function := by
  induction rank with
  | zero => rw [orderedDerivative_zero, orderedDerivative_zero]
  | succ rank induction =>
    funext point
    rw [orderedDerivative_succ rank word _
      (convolution_contDiff kernel function smoothness compactSupport integrableLocally), induction (Fin.tail word),
      convolution_direction _ function (orderedDerivative_contDiff rank (Fin.tail word) kernel smoothness)
        (orderedDerivative_compactSupport rank (Fin.tail word) kernel compactSupport) integrableLocally]
    apply congrArg (fun scalarKernel : Spatial → ℝ => convolution scalarKernel function point)
    funext source
    exact (orderedDerivative_succ rank word kernel smoothness source).symm

theorem pointwiseGoal : PointwiseGoal := by
  intro Value _normed _inner _complete kernel smoothness compactSupport field
  have integrableLocally := localGoal Value field
  refine ⟨convolution_integrable kernel field smoothness.continuous compactSupport integrableLocally,
    convolution_contDiff kernel field smoothness compactSupport integrableLocally, ?_⟩
  intro rank word point
  refine ⟨convolution_integrable (orderedDerivative rank word kernel) field
    (orderedDerivative_contDiff rank word kernel smoothness).continuous
    (orderedDerivative_compactSupport rank word kernel compactSupport) integrableLocally point, ?_⟩
  exact congrFun (orderedDerivative_convolution kernel field smoothness compactSupport integrableLocally rank word) point

end Grad.Mollifier.Pointwise
