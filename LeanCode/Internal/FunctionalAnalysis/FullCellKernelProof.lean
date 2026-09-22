import CellFieldExchange

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 fieldCellProjection)
open scoped BigOperators Topology

namespace Grad.FullCellKernel

variable {Parameter : Type*} [MeasurableSpace Parameter]
  {measure : Measure Parameter} [SigmaFinite measure]
  {inputDimension outputDimension : ℕ} {domain : Set Spatial}
  (data : L2KernelData measure inputDimension outputDimension domain)

def integratedWeight (output input : ℤ) : ℝ := ∫ parameter, data.weight output input parameter ∂measure

omit [SigmaFinite measure] in
theorem integratedWeight_nonneg (output input : ℤ) : 0 ≤ integratedWeight data output input :=
  integral_nonneg (data.weightNonnegative output input)

theorem entry_norm_le (output input : ℤ) : ‖entry data output input‖ ≤ integratedWeight data output input :=
  Grad.KernelIntegral.integralKernelCLM_norm_le measure data.domainMeasurable data.orthogonal
    data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
    (data.coefficientMeasurable output input) (data.weightMeasurable output input)
    (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input)

def coordinateKernel : CoordinateFields inputDimension domain →L[ℂ] CoordinateFields outputDimension domain :=
  Grad.SchurKernel.Discrete.discreteActionCLM (entry data) (integratedWeight data)
    data.rowBound data.columnBound data.rowNonnegative data.columnNonnegative
    (integratedWeight_nonneg data) (entry_norm_le data) data.rowsSummable data.columnsSummable
    data.rows data.columns

theorem coordinateKernel_norm_apply (fields : CoordinateFields inputDimension domain) :
    ‖coordinateKernel data fields‖ ≤ Real.sqrt (data.rowBound * data.columnBound) * ‖fields‖ :=
  Grad.SchurKernel.Discrete.norm_discreteActionCLM_apply_le (entry data) (integratedWeight data)
    data.rowBound data.columnBound data.rowNonnegative data.columnNonnegative
    (integratedWeight_nonneg data) (entry_norm_le data) data.rowsSummable data.columnsSummable
    data.rows data.columns fields

def kernel : FieldL2 inputDimension domain →L[ℂ] FieldL2 outputDimension domain :=
  (exchange outputDimension domain).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((coordinateKernel data).comp (exchange inputDimension domain).toLinearIsometry.toContinuousLinearMap)

theorem kernel_norm_apply (field : FieldL2 inputDimension domain) :
    ‖kernel data field‖ ≤ Real.sqrt (data.rowBound * data.columnBound) * ‖field‖ := by
  change ‖(exchange outputDimension domain).symm
    (coordinateKernel data (exchange inputDimension domain field))‖ ≤ _
  rw [(exchange outputDimension domain).symm.norm_map]
  simpa only [(exchange inputDimension domain).norm_map] using
    coordinateKernel_norm_apply data (exchange inputDimension domain field)

theorem kernel_norm_le : ‖kernel data‖ ≤ Real.sqrt (data.rowBound * data.columnBound) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (kernel_norm_apply data)

theorem kernel_coordinate (field : FieldL2 inputDimension domain) (output : ℤ) :
    fieldCellProjection outputDimension domain output (kernel data field) =
      ∑' input : ℤ, entry data output input (fieldCellProjection inputDimension domain input field) := by
  change fieldCellProjection outputDimension domain output
    ((exchange outputDimension domain).symm (coordinateKernel data (exchange inputDimension domain field))) = _
  rw [exchange_symm_coordinate]
  rfl

theorem kernel_finite_cells (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) (output : ℤ) :
    fieldCellProjection outputDimension domain output (kernel data field) =
      ∑ input ∈ cells, entry data output input (fieldCellProjection inputDimension domain input field) := by
  rw [kernel_coordinate]
  exact tsum_eq_sum (fun input outside => by rw [support input outside, map_zero])

theorem entry_field_ae (field : FieldL2 inputDimension domain) (output input : ℤ) :
    ∀ᵐ point ∂volume.restrict domain,
      entry data output input (fieldCellProjection inputDimension domain input field) point =
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure :=
  Filter.EventuallyEq.trans
    (Grad.KernelIntegral.integralKernelCLM_apply_ae measure data.domainMeasurable data.orthogonal
      data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
      (data.coefficientMeasurable output input) (data.weightMeasurable output input)
      (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input)
      (fieldCellProjection inputDimension domain input field))
    (Grad.KernelIntegral.integralAction_congr_ae measure data.domainMeasurable data.orthogonal
      data.invariant data.actionMeasurable (data.coefficient output input)
      ((Grad.GenericCarriers.fieldCellProjection_ae inputDimension domain field).mono
        (fun _ coordinates => coordinates input)))

theorem kernel_core_ae (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      kernel data field point output = ∑ input ∈ cells,
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure := by
  apply ae_all_iff.mpr
  intro output
  have allEntries : ∀ᵐ point ∂volume.restrict domain, ∀ input : ℤ,
      entry data output input (fieldCellProjection inputDimension domain input field) point =
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure :=
    ae_all_iff.mpr (entry_field_ae data field output)
  filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae outputDimension domain (kernel data field),
    Lp.coeFn_fun_finsetSum cells
      (fun input => entry data output input (fieldCellProjection inputDimension domain input field)),
    allEntries] with point coordinates sumLiteral entries
  rw [← coordinates output, kernel_finite_cells data field cells support output]
  exact sumLiteral.trans (Finset.sum_congr rfl (fun input _ => entries input))

theorem kernel_strong_sections (field : FieldL2 inputDimension domain) :
    Filter.Tendsto (fun cells : Finset ℤ =>
      Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue outputDimension) cells
        (kernel data (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain)
          (PhysicalValue inputDimension) cells field))) Filter.atTop (𝓝 (kernel data field)) :=
  Grad.CellProjections.Generic.rectangular_sections (volume.restrict domain) (kernel data) field

theorem kernel_spec : KernelSpec data (kernel data) :=
  ⟨kernel_norm_le data, kernel_coordinate data, kernel_core_ae data, kernel_strong_sections data⟩

theorem kernel_consumer : KernelGoal := by
  intro Parameter measurableParameter measure sigmaFinite inputDimension outputDimension domain data
  exact ⟨kernel data, kernel_spec data⟩

end Grad.FullCellKernel
