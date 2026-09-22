import CK1Pair

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.RepresentedKernel.Composition

theorem cellProjection_cutoff (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    fieldCellProjection dimension domain cell
        (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue dimension) cells field) =
      if cell ∈ cells then fieldCellProjection dimension domain cell field else 0 := by
  have projectionCoordinates := Grad.CellProjections.Generic.field_projection_coordinate
    (PhysicalValue dimension) (volume.restrict domain) cells field
  have projectedCoordinates := fieldCellProjection_ae dimension domain
    (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue dimension) cells field)
  by_cases membership : cell ∈ cells
  · rw [if_pos membership]
    apply Lp.ext
    filter_upwards [projectionCoordinates, projectedCoordinates, fieldCellProjection_ae dimension domain field]
      with point projectionAt projectedAt originalAt
    rw [projectedAt cell, projectionAt cell, if_pos membership, originalAt cell]
  · rw [if_neg membership]
    apply Lp.ext
    filter_upwards [projectionCoordinates, projectedCoordinates,
      Lp.coeFn_zero (PhysicalValue dimension) 2 (volume.restrict domain)] with point projectionAt projectedAt zeroAt
    rw [projectedAt cell, projectionAt cell, if_neg membership, zeroAt]
    rfl

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def partialComposite (cells : Finset ℤ) : FieldL2 inputDimension domain →L[ℂ] FieldL2 outputDimension domain :=
  (Grad.FullCellKernel.kernel outer).comp
    ((Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue middleDimension) cells).comp
      (Grad.FullCellKernel.kernel inner))

theorem partialComposite_strong (field : FieldL2 inputDimension domain) :
    Filter.Tendsto (fun cells : Finset ℤ => partialComposite outer inner cells field)
      Filter.atTop (𝓝 (Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field))) :=
  (Grad.FullCellKernel.kernel outer).continuous.continuousAt.tendsto.comp
    (Grad.CellProjections.Generic.field_strong (volume.restrict domain) (PhysicalValue middleDimension)
      (Grad.FullCellKernel.kernel inner field))

theorem partialComposite_error (cells : Finset ℤ) (field : FieldL2 inputDimension domain) :
    ‖partialComposite outer inner cells field -
        Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field)‖ ≤
      ‖Grad.FullCellKernel.kernel outer‖ *
        ‖Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue middleDimension) cells
          (Grad.FullCellKernel.kernel inner field) - Grad.FullCellKernel.kernel inner field‖ := by
  change ‖Grad.FullCellKernel.kernel outer _ - Grad.FullCellKernel.kernel outer _‖ ≤ _
  rw [← map_sub]
  exact (Grad.FullCellKernel.kernel outer).le_opNorm _

theorem partialComposite_norm_le (cells : Finset ℤ) :
    ‖partialComposite outer inner cells‖ ≤
      Real.sqrt (outer.rowBound * outer.columnBound) * Real.sqrt (inner.rowBound * inner.columnBound) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  intro field
  change ‖Grad.FullCellKernel.kernel outer _‖ ≤ _
  calc
    _ ≤ Real.sqrt (outer.rowBound * outer.columnBound) *
        ‖Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue middleDimension) cells
          (Grad.FullCellKernel.kernel inner field)‖ := Grad.FullCellKernel.kernel_norm_apply outer _
    _ ≤ Real.sqrt (outer.rowBound * outer.columnBound) * ‖Grad.FullCellKernel.kernel inner field‖ :=
      mul_le_mul_of_nonneg_left
        (Grad.CellProjections.Generic.field_projection_norm_apply (PhysicalValue middleDimension)
          (volume.restrict domain) cells (Grad.FullCellKernel.kernel inner field)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (outer.rowBound * outer.columnBound) *
        (Real.sqrt (inner.rowBound * inner.columnBound) * ‖field‖) :=
      mul_le_mul_of_nonneg_left (Grad.FullCellKernel.kernel_norm_apply inner field) (Real.sqrt_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem partialComposite_coordinate (cells : Finset ℤ) (field : FieldL2 inputDimension domain) (output : ℤ) :
    fieldCellProjection outputDimension domain output (partialComposite outer inner cells field) =
      ∑ middle ∈ cells, Grad.FullCellKernel.entry outer output middle
        (fieldCellProjection middleDimension domain middle (Grad.FullCellKernel.kernel inner field)) := by
  change fieldCellProjection outputDimension domain output
    (Grad.FullCellKernel.kernel outer
      (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue middleDimension) cells
        (Grad.FullCellKernel.kernel inner field))) = _
  rw [Grad.FullCellKernel.kernel_finite_cells outer _ cells (fun cell outside => by
    rw [cellProjection_cutoff, if_neg outside])]
  apply Finset.sum_congr rfl
  intro middle membership
  rw [cellProjection_cutoff, if_pos membership]

theorem partialComposite_finite_input (middleCells inputCells : Finset ℤ)
    (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) (output : ℤ) :
    fieldCellProjection outputDimension domain output (partialComposite outer inner middleCells field) =
      ∑ middle ∈ middleCells, ∑ input ∈ inputCells,
        pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field) := by
  rw [partialComposite_coordinate]
  apply Finset.sum_congr rfl
  intro middle _membership
  rw [Grad.FullCellKernel.kernel_finite_cells inner field inputCells support middle, map_sum]
  apply Finset.sum_congr rfl
  intro input _membership
  rw [pairOperator_composition, ContinuousLinearMap.comp_apply]

theorem composition_coordinate_hasSum (inputCells : Finset ℤ) (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) (output : ℤ) :
    HasSum (fun middle : ℤ => ∑ input ∈ inputCells,
      pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field))
      (fieldCellProjection outputDimension domain output
        (Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field))) := by
  have limit := (fieldCellProjection outputDimension domain output).continuous.continuousAt.tendsto.comp
    (partialComposite_strong outer inner field)
  change Filter.Tendsto (fun cells : Finset ℤ => ∑ middle ∈ cells, ∑ input ∈ inputCells,
    pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field))
    Filter.atTop (𝓝 _)
  exact limit.congr' (Filter.Eventually.of_forall (fun cells =>
    partialComposite_finite_input outer inner cells inputCells field support output))

end Grad.RepresentedKernel.Composition
