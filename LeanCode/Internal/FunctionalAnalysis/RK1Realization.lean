import RK1Moments

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel

variable {Parameter : Type*} [MeasurableSpace Parameter]
  {measure : Measure Parameter} [SigmaFinite measure]
  {inputDimension outputDimension : ℕ} {domain : Set Spatial}
  (data : RawKernelData measure inputDimension outputDimension domain)

def operator (multiindex : ℕ × ℕ) (moment : ℕ) :
    FieldL2 inputDimension domain →L[ℂ] FieldL2 outputDimension domain :=
  Grad.FullCellKernel.kernel (l2Data data multiindex moment)

theorem operator_norm_le (multiindex : ℕ × ℕ) (moment : ℕ) :
    ‖operator data multiindex moment‖ ≤
      Real.sqrt (data.rowBound multiindex moment * data.columnBound multiindex moment) :=
  Grad.FullCellKernel.kernel_norm_le (l2Data data multiindex moment)

theorem operator_norm_apply (multiindex : ℕ × ℕ) (moment : ℕ)
    (field : FieldL2 inputDimension domain) :
    ‖operator data multiindex moment field‖ ≤
      Real.sqrt (data.rowBound multiindex moment * data.columnBound multiindex moment) * ‖field‖ :=
  Grad.FullCellKernel.kernel_norm_apply (l2Data data multiindex moment) field

theorem operator_coordinate (multiindex : ℕ × ℕ) (moment : ℕ)
    (field : FieldL2 inputDimension domain) (output : ℤ) :
    fieldCellProjection outputDimension domain output (operator data multiindex moment field) =
      ∑' input : ℤ, Grad.FullCellKernel.entry (l2Data data multiindex moment) output input
        (fieldCellProjection inputDimension domain input field) :=
  Grad.FullCellKernel.kernel_coordinate (l2Data data multiindex moment) field output

theorem operator_core_ae (multiindex : ℕ × ℕ) (moment : ℕ)
    (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      operator data multiindex moment field point output = ∑ input ∈ cells,
        ∫ parameter, Grad.CellWeights.derivativeFactor moment (output - input) •
          coefficientDerivative multiindex (data.coefficient output input) (parameter, point)
            (field (data.orthogonal parameter point) input) ∂measure :=
  Grad.FullCellKernel.kernel_core_ae (l2Data data multiindex moment) field cells support

theorem operator_zero_core_ae (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      operator data (0, 0) 0 field point output = ∑ input ∈ cells,
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure := by
  simpa only [Grad.CellWeights.derivativeFactor, pow_zero, one_smul,
    coefficientDerivative_zero] using operator_core_ae data (0, 0) 0 field cells support

theorem operator_strong_sections (multiindex : ℕ × ℕ) (moment : ℕ)
    (field : FieldL2 inputDimension domain) :
    Filter.Tendsto (fun cells : Finset ℤ =>
      Grad.CellProjections.Generic.fieldProjection (volume.restrict domain)
        (PhysicalValue outputDimension) cells
        (operator data multiindex moment
          (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain)
            (PhysicalValue inputDimension) cells field))) Filter.atTop
      (𝓝 (operator data multiindex moment field)) :=
  Grad.FullCellKernel.kernel_strong_sections (l2Data data multiindex moment) field

theorem operator_spec (multiindex : ℕ × ℕ) (moment : ℕ) :
    Grad.FullCellKernel.KernelSpec (l2Data data multiindex moment)
      (operator data multiindex moment) :=
  Grad.FullCellKernel.kernel_spec (l2Data data multiindex moment)

end Grad.RepresentedKernel
