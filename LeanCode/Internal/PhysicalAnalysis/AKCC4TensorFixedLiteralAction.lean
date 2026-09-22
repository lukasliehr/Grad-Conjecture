import AKCC3FixedCovectorEntries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 1800

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel.SpatialProduct

theorem startupTensorFieldEquiv_symm_ae (dimension rank : ℕ)
    (field : StartupL2 (startupTensorDimension dimension rank)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (WithLp.toLp 2 (fun word : DerivativeIndex rank =>
        (startupTensorFieldEquiv dimension rank).symm field word point cell) : Tensor rank (PhysicalValue dimension)) =
      (startupTensorValueEquiv dimension rank).symm (field point cell) := by
  have represented := startupTensorFieldEquiv_ae dimension rank ((startupTensorFieldEquiv dimension rank).symm field)
  rw [LinearIsometryEquiv.apply_symm_apply] at represented
  filter_upwards [represented] with point same
  intro cell
  exact ((startupTensorValueEquiv dimension rank).symm_apply_apply _).symm.trans
    (congrArg (startupTensorValueEquiv dimension rank).symm (same cell).symm)

theorem startupFixedTensor_coordinate_ae {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (integrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (fields : Tensor rank (StartupL2 input)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, ∀ word : DerivativeIndex rank,
      startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient measurable integrable fields word point cell =
      ∫ parameter, coefficient parameter (∑ target : DerivativeIndex rank,
        (chainFactor rank (orthogonal parameter) word target : ℂ) • fields target (orthogonal parameter point) cell) ∂measure := by
  let flat := startupTensorFieldEquiv input rank fields
  let lifted := fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)
  let kernel := Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable lifted measurable integrable)
  have sourceSame : (fun point => fun cell => flat point cell) =ᵐ[volume.restrict openUnitDisk]
      (fun point => fun cell => startupTensorValueEquiv input rank
        (WithLp.toLp 2 (fun word => fields word point cell))) :=
    (startupTensorFieldEquiv_ae input rank fields).mono (fun _ same => funext same)
  filter_upwards [startupTensorFieldEquiv_symm_ae output rank (kernel flat),
    startupFixed_coordinate_ae measure orthogonal invariant actionMeasurable lifted measurable integrable flat,
    startupFixed_rows_integrable measure orthogonal invariant actionMeasurable lifted measurable integrable flat,
    Grad.KernelIntegral.transported_ae_eq_sections measure openUnitDisk_isOpen.measurableSet orthogonal invariant actionMeasurable sourceSame]
    with point outputSame action rows sourceRows
  intro cell word
  let projection : PhysicalValue (startupTensorDimension output rank) →L[ℂ] PhysicalValue output :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : DerivativeIndex rank => PhysicalValue output) word).comp
      (startupTensorValueEquiv output rank).symm.toLinearIsometry.toContinuousLinearMap
  have atOutput := congrArg (fun values : Tensor rank (PhysicalValue output) => values word) (outputSame cell)
  change startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient measurable integrable fields word point cell =
    projection (kernel flat point cell) at atOutput
  rw [atOutput, action cell, ← projection.integral_comp_comm (rows cell)]
  apply integral_congr_ae
  filter_upwards [sourceRows] with parameter sourceRow
  rw [congrFun sourceRow cell]
  change (startupTensorValueEquiv output rank).symm
      (startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)
        (startupTensorValueEquiv input rank (WithLp.toLp 2 (fun target => fields target (orthogonal parameter point) cell)))) word = _
  rw [startupCovectorCoefficient_apply]
  rfl

end Grad.CartesianStartup
