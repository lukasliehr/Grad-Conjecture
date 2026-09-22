import CK2Realization

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.RepresentedKernel.Composition.Countable

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

theorem literalCore_consumer (inputCells : Finset ℤ) (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field) point output =
        ∑ input ∈ inputCells, ∫ parameter : ℤ × (Outer × Inner),
          outer.coefficient output parameter.1 (parameter.2.1, point)
            (inner.coefficient parameter.1 input (parameter.2.2, outer.orthogonal parameter.2.1 point)
              (field (inner.orthogonal parameter.2.2 (outer.orthogonal parameter.2.1 point)) input))
          ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure) := by
  have identity := Grad.FullCellKernel.kernel_core_ae (composedData outer inner) field inputCells support
  rw [composedKernel_eq] at identity
  exact identity

theorem representation_consumer :
    ∃ data : Grad.FullCellKernel.L2KernelData
        ((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) inputDimension outputDimension domain,
      data.coefficient = countCoefficient outer inner ∧ data.weight = countWeight outer inner ∧
      data.orthogonal = countOrthogonal outer inner ∧
      data.rowBound = outer.rowBound * inner.rowBound ∧
      data.columnBound = outer.columnBound * inner.columnBound ∧
      Grad.FullCellKernel.kernel data = (Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner) ∧
      Grad.FullCellKernel.KernelSpec data ((Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner)) :=
  ⟨composedData outer inner, rfl, rfl, rfl, rfl, rfl, composedKernel_eq outer inner, composedKernel_spec outer inner⟩

theorem coefficientOrder_consumer (output input middle : ℤ) (outerParameter : Outer) (innerParameter : Inner)
    (point : Spatial) :
    (composedData outer inner).coefficient output input ((middle, outerParameter, innerParameter), point) =
      (outer.coefficient output middle (outerParameter, point)).comp
        (inner.coefficient middle input (innerParameter, outer.orthogonal outerParameter point)) ∧
    (composedData outer inner).orthogonal (middle, outerParameter, innerParameter) point =
      inner.orthogonal innerParameter (outer.orthogonal outerParameter point) := ⟨rfl, rfl⟩

theorem rectangularSections_consumer (field : FieldL2 inputDimension domain) :
    Filter.Tendsto (fun cells : Finset ℤ =>
      Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue outputDimension) cells
        (Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner
          (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue inputDimension) cells field))))
      Filter.atTop (𝓝 (Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field))) :=
  Grad.CellProjections.Generic.rectangular_sections (volume.restrict domain)
    ((Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner)) field

end Grad.RepresentedKernel.Composition.Countable
