import CK2Entries
import CK1Consumer

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

theorem composedKernel_finite_input (inputCells : Finset ℤ) (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) :
    Grad.FullCellKernel.kernel (composedData outer inner) field =
      Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field) := by
  apply (Grad.FullCellKernel.exchange outputDimension domain).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.exchange_coordinate, Grad.FullCellKernel.exchange_coordinate]
  calc
    _ = ∑ input ∈ inputCells, Grad.FullCellKernel.entry (composedData outer inner) output input
        (fieldCellProjection inputDimension domain input field) :=
      Grad.FullCellKernel.kernel_finite_cells (composedData outer inner) field inputCells support output
    _ = ∑ input ∈ inputCells, ∑' middle : ℤ,
        pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field) := by
      apply Finset.sum_congr rfl
      intro input _membership
      rw [composedEntry_eq, combinedEntry_apply]
    _ = ∑' middle : ℤ, ∑ input ∈ inputCells,
        pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field) :=
      (Summable.tsum_finsetSum (fun input _membership =>
        (pairField_norm_summable outer inner output input (fieldCellProjection inputDimension domain input field)).of_norm)).symm
    _ = _ := fullMiddleSeries_consumer outer inner inputCells field support output

theorem composedKernel_eq :
    Grad.FullCellKernel.kernel (composedData outer inner) =
      (Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner) := by
  apply ContinuousLinearMap.ext
  intro field
  have cutoffLimit := Grad.CellProjections.Generic.field_strong (volume.restrict domain)
    (PhysicalValue inputDimension) field
  have firstLimit := (Grad.FullCellKernel.kernel (composedData outer inner)).continuous.continuousAt.tendsto.comp cutoffLimit
  have secondLimit := ((Grad.FullCellKernel.kernel outer).comp
    (Grad.FullCellKernel.kernel inner)).continuous.continuousAt.tendsto.comp cutoffLimit
  apply tendsto_nhds_unique firstLimit
  exact secondLimit.congr' (Filter.Eventually.of_forall (fun cells : Finset ℤ =>
    (composedKernel_finite_input outer inner cells _ (fun input outside => by
      rw [cellProjection_cutoff, if_neg outside])).symm))

theorem composedKernel_norm_le :
    ‖(Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner)‖ ≤
      Real.sqrt ((outer.rowBound * inner.rowBound) * (outer.columnBound * inner.columnBound)) := by
  rw [← composedKernel_eq]
  exact Grad.FullCellKernel.kernel_norm_le (composedData outer inner)

theorem composedKernel_spec :
    Grad.FullCellKernel.KernelSpec (composedData outer inner)
      ((Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner)) := by
  rw [← composedKernel_eq]
  exact Grad.FullCellKernel.kernel_spec (composedData outer inner)

end Grad.RepresentedKernel.Composition.Countable
