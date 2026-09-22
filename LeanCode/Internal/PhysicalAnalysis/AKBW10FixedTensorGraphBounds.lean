import AKBW9CovectorCoefficientContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupTensorFirstEquiv_symm_values (dimension rank : ℕ)
    (field : StartupFirst (startupTensorDimension dimension rank)) :
    startupTensorFirstValues ((startupTensorFirstEquiv dimension rank).symm field) =
      (startupTensorFieldEquiv dimension rank).symm (startupFirstValue field) := by
  apply PiLp.ext
  intro word
  exact startupTensorFirstSeparate_base field word

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (integrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)

theorem startupFixedTensorFirst_base (field : StartupTensorFirst input rank) :
    startupTensorFirstValues
      (startupFixedTensorFirst measure rank orthogonal invariant actionMeasurable coefficient measurable integrable field) =
      startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient measurable integrable
        (startupTensorFirstValues field) := by
  change startupTensorFirstValues ((startupTensorFirstEquiv output rank).symm
    (startupFixedFirstGraph measure orthogonal invariant actionMeasurable
      (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter))
      measurable integrable (startupTensorFirstEquiv input rank field))) = _
  rw [startupTensorFirstEquiv_symm_values]
  unfold startupFirstValue
  rw [startupFixedFirstGraph_base]
  rw [show Grad.WeightedJets.base (startupTensorDimension input rank) 1 openUnitDisk (fun _ => 0)
      (startupTensorFirstEquiv input rank field) = _ from startupTensorFirstEquiv_base input rank field]
  rfl

theorem startupFixedTensorKernel_norm (originalIntegrable : Integrable coefficient measure) :
    ‖startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient measurable integrable‖ ≤
      ∫ parameter, ‖coefficient parameter‖ ∂measure := by
  have integralBound : (∫ parameter, ‖startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)‖ ∂measure) ≤
      ∫ parameter, ‖coefficient parameter‖ ∂measure :=
    integral_mono integrable.norm originalIntegrable.norm (fun parameter => startupCovectorCoefficient_norm rank _ _)
  have kernelBound := Grad.FullCellKernel.kernel_norm_le
    (startupFixedKernelData measure orthogonal invariant actionMeasurable
      (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measurable integrable)
  change ‖Grad.FullCellKernel.kernel _‖ ≤ Real.sqrt
    ((∫ parameter, ‖startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)‖ ∂measure) *
      ∫ parameter, ‖startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)‖ ∂measure) at kernelBound
  rw [Real.sqrt_mul_self (integral_nonneg (fun _ => norm_nonneg _))] at kernelBound
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => norm_nonneg _))
  intro fields
  change ‖(startupTensorFieldEquiv output rank).symm
    (Grad.FullCellKernel.kernel _ (startupTensorFieldEquiv input rank fields))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by rw [LinearIsometryEquiv.norm_map]; exact mul_le_mul_of_nonneg_right (kernelBound.trans integralBound) (norm_nonneg _))

theorem startupFixedTensorFirst_norm (originalIntegrable : Integrable coefficient measure) :
    ‖startupFixedTensorFirst measure rank orthogonal invariant actionMeasurable coefficient measurable integrable‖ ≤
      7 * ∫ parameter, ‖coefficient parameter‖ ∂measure := by
  have integralBound : (∫ parameter, ‖startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)‖ ∂measure) ≤
      ∫ parameter, ‖coefficient parameter‖ ∂measure :=
    integral_mono integrable.norm originalIntegrable.norm (fun parameter => startupCovectorCoefficient_norm rank _ _)
  have kernelBound := startupFixedFirstGraph_norm measure orthogonal invariant actionMeasurable
    (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measurable integrable
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (integral_nonneg (fun _ => norm_nonneg _)))
  intro fields
  change ‖(startupTensorFirstEquiv output rank).symm
    (startupFixedFirstGraph measure orthogonal invariant actionMeasurable
      (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter))
      measurable integrable (startupTensorFirstEquiv input rank fields))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right
        (kernelBound.trans (mul_le_mul_of_nonneg_left integralBound (by norm_num))) (norm_nonneg _))

end Grad.CartesianStartup
