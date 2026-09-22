import AKBW7TensorFirstGraphEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)

/-- Literal fixed-kernel coefficient on all ordered covector indices. Both
isometries merely identify finite Hilbert products with physical values. -/
def startupCovectorCoefficient {input output : ℕ} (rank : ℕ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (coefficient : OperatorValue input output) :
    OperatorValue (startupTensorDimension input rank) (startupTensorDimension output rank) :=
  (startupTensorValueEquiv output rank).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hilbertLift (Index := DerivativeIndex rank) coefficient).comp
      ((Grad.TensorAction.Generic.covectorEquivalence (PhysicalValue input) rank orthogonal).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (startupTensorValueEquiv input rank).symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem startupCovectorCoefficient_apply {input output : ℕ} (rank : ℕ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (coefficient : OperatorValue input output)
    (tensor : Tensor rank (PhysicalValue input)) (word : DerivativeIndex rank) :
    (startupTensorValueEquiv output rank).symm
        (startupCovectorCoefficient rank orthogonal coefficient (startupTensorValueEquiv input rank tensor)) word =
      coefficient (∑ source : DerivativeIndex rank,
        ((∏ position : Fin rank, orthogonal (spatialDirection (word position)) (source position) : ℝ) : ℂ) • tensor source) := by
  change (startupTensorValueEquiv output rank).symm
    (startupTensorValueEquiv output rank
      (hilbertLift (Index := DerivativeIndex rank) coefficient
        (Grad.TensorAction.Generic.covectorEquivalence (PhysicalValue input) rank orthogonal
          ((startupTensorValueEquiv input rank).symm (startupTensorValueEquiv input rank tensor))))) word = _
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    hilbertLift_apply, Grad.TensorAction.Generic.covectorEquivalence_coordinate]
  simp only [Complex.ofReal_prod]

theorem startupCovectorCoefficient_norm {input output : ℕ} (rank : ℕ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (coefficient : OperatorValue input output) :
    ‖startupCovectorCoefficient rank orthogonal coefficient‖ ≤ ‖coefficient‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg coefficient)
  intro vector
  change ‖startupTensorValueEquiv output rank
    (hilbertLift (Index := DerivativeIndex rank) coefficient
      (Grad.TensorAction.Generic.covectorEquivalence (PhysicalValue input) rank orthogonal
        ((startupTensorValueEquiv input rank).symm vector)))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (hilbertLiftLinear_norm_le coefficient _).trans_eq
    (by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map])

/-- Genuine rank lift of the fixed full-cell kernel. The coefficient bound is
independent of rank; no entrywise estimate or covector count is inserted. -/
def startupFixedTensorKernel {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (integrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure) :
    Tensor rank (StartupL2 input) →L[ℂ] Tensor rank (StartupL2 output) :=
  (startupTensorFieldEquiv output rank).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Grad.FullCellKernel.kernel
      (Grad.GaugeCoefficients.Physical.RadialLedger.startupFixedKernelData measure orthogonal invariant actionMeasurable
        (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measurable integrable)).comp
      (startupTensorFieldEquiv input rank).toContinuousLinearEquiv.toContinuousLinearMap)

def startupFixedTensorFirst {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (integrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure) :
    StartupTensorFirst input rank →L[ℂ] StartupTensorFirst output rank :=
  (startupTensorFirstEquiv output rank).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((startupFixedFirstGraph measure orthogonal invariant actionMeasurable
      (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measurable integrable).comp
      (startupTensorFirstEquiv input rank).toContinuousLinearEquiv.toContinuousLinearMap)

end Grad.CartesianStartup
