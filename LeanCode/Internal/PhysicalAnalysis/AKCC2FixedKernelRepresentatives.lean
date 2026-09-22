import AKCC1LiteralFixedKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

include invariant actionMeasurable measurable integrable

theorem startupFixed_rows_integrable (field : StartupL2 input) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      Integrable (fun parameter => coefficient parameter (field (orthogonal parameter point) cell)) measure := by
  apply ae_all_iff.mpr
  intro cell
  let data := startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable
  have rows := Grad.KernelIntegral.row_integrable_and_sq_bound measure data.domainMeasurable data.orthogonal
    data.invariant data.actionMeasurable (data.coefficient cell cell) (data.weight cell cell)
    (data.coefficientMeasurable cell cell) (data.weightMeasurable cell cell)
    (data.weightNonnegative cell cell) (data.weightIntegrable cell cell) (data.domination cell cell)
    (fieldCellProjection input openUnitDisk cell field)
  have represented : (fun point => fieldCellProjection input openUnitDisk cell field point) =ᵐ[volume.restrict openUnitDisk]
      (fun point => field point cell) :=
    (fieldCellProjection_ae input openUnitDisk field).mono (fun _ same => same cell)
  filter_upwards [rows, Grad.KernelIntegral.transported_ae_eq_sections measure openUnitDisk_isOpen.measurableSet
    orthogonal invariant actionMeasurable represented] with point row coordinates
  have integrableRow := row.1
  simp only [data, startupFixedKernelData, if_true] at integrableRow
  apply integrableRow.congr
  filter_upwards [coordinates] with parameter same
  rw [same]

theorem startupFixed_representative (field : StartupL2 input)
    (raw : Spatial → ℤ → PhysicalValue input)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, field point cell = raw point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable
        coefficient measurable integrable) field point cell =
      ∫ parameter, coefficient parameter (raw (orthogonal parameter point) cell) ∂measure := by
  have equality : (fun point => fun cell => field point cell) =ᵐ[volume.restrict openUnitDisk] raw :=
    same.mono (fun _ equal => funext equal)
  filter_upwards [startupFixed_coordinate_ae measure orthogonal invariant actionMeasurable coefficient measurable integrable field,
    Grad.KernelIntegral.transported_ae_eq_sections measure openUnitDisk_isOpen.measurableSet
      orthogonal invariant actionMeasurable equality] with point action represented
  intro cell
  rw [action cell]
  apply integral_congr_ae
  filter_upwards [represented] with parameter equal
  rw [congrFun equal cell]

end Grad.CartesianStartup
