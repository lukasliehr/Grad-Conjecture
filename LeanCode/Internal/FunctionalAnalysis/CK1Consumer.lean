import CK1Sections

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.RepresentedKernel.Composition

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def pairFieldIntegral (field : FieldL2 inputDimension domain) (output middle input : ℤ) (point : Spatial) :
    PhysicalValue outputDimension :=
  ∫ parameter : Outer × Inner, outer.coefficient output middle (parameter.1, point)
    (inner.coefficient middle input (parameter.2, outer.orthogonal parameter.1 point)
      (field (inner.orthogonal parameter.2 (outer.orthogonal parameter.1 point)) input))
    ∂outerMeasure.prod innerMeasure

theorem pairOperator_field_ae (field : FieldL2 inputDimension domain) (output middle input : ℤ) :
    ∀ᵐ point ∂volume.restrict domain,
      pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field) point =
        pairFieldIntegral outer inner field output middle input point :=
  Filter.EventuallyEq.trans
    (pairOperator_ae outer inner output middle input (fieldCellProjection inputDimension domain input field))
    (Grad.KernelIntegral.integralAction_congr_ae (outerMeasure.prod innerMeasure) outer.domainMeasurable
      (pairOrthogonal outer inner) (pairOrthogonal_invariant outer inner) (pair_action_measurable outer inner)
      (pairCoefficient outer inner output middle input)
      ((fieldCellProjection_ae inputDimension domain field).mono (fun _ coordinates => coordinates input)))

theorem partialComposite_core_ae (middleCells inputCells : Finset ℤ)
    (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      partialComposite outer inner middleCells field point output =
        ∑ middle ∈ middleCells, ∑ input ∈ inputCells,
          pairFieldIntegral outer inner field output middle input point := by
  apply ae_all_iff.mpr
  intro output
  have allEntries : ∀ᵐ point ∂volume.restrict domain, ∀ middle input : ℤ,
      pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field) point =
        pairFieldIntegral outer inner field output middle input point :=
    ae_all_iff.mpr (fun middle => ae_all_iff.mpr (pairOperator_field_ae outer inner field output middle))
  have innerSums : ∀ᵐ point ∂volume.restrict domain, ∀ middle : ℤ,
      (∑ input ∈ inputCells, pairOperator outer inner output middle input
        (fieldCellProjection inputDimension domain input field)) point =
      ∑ input ∈ inputCells, pairOperator outer inner output middle input
        (fieldCellProjection inputDimension domain input field) point :=
    ae_all_iff.mpr (fun middle => Lp.coeFn_fun_finsetSum inputCells
      (fun input => pairOperator outer inner output middle input
        (fieldCellProjection inputDimension domain input field)))
  filter_upwards [fieldCellProjection_ae outputDimension domain (partialComposite outer inner middleCells field),
    allEntries, innerSums, Lp.coeFn_fun_finsetSum middleCells
      (fun middle => ∑ input ∈ inputCells, pairOperator outer inner output middle input
        (fieldCellProjection inputDimension domain input field))]
    with point coordinates entries innerLiteral outerLiteral
  rw [← coordinates output, partialComposite_finite_input outer inner middleCells inputCells field support output,
    outerLiteral]
  apply Finset.sum_congr rfl
  intro middle _membership
  rw [innerLiteral middle]
  exact Finset.sum_congr rfl (fun input _membership => entries middle input)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem retainedParameter_consumer (field : FieldL2 inputDimension domain) (output middle input : ℤ)
    (parameter : Outer × Inner) (point : Spatial) :
    pairCoefficient outer inner output middle input (parameter, point)
        (field (pairOrthogonal outer inner parameter point) input) =
      outer.coefficient output middle (parameter.1, point)
        (inner.coefficient middle input (parameter.2, outer.orthogonal parameter.1 point)
          (field (inner.orthogonal parameter.2 (outer.orthogonal parameter.1 point)) input)) := rfl

theorem strongComposition_consumer (field : FieldL2 inputDimension domain) :
    Filter.Tendsto (fun cells : Finset ℤ => partialComposite outer inner cells field) Filter.atTop
      (𝓝 (((Grad.FullCellKernel.kernel outer).comp (Grad.FullCellKernel.kernel inner)) field)) :=
  partialComposite_strong outer inner field

theorem fullMiddleSeries_consumer (inputCells : Finset ℤ) (field : FieldL2 inputDimension domain)
    (support : ∀ input ∉ inputCells, fieldCellProjection inputDimension domain input field = 0) (output : ℤ) :
    (∑' middle : ℤ, ∑ input ∈ inputCells,
      pairOperator outer inner output middle input (fieldCellProjection inputDimension domain input field)) =
      fieldCellProjection outputDimension domain output
        (Grad.FullCellKernel.kernel outer (Grad.FullCellKernel.kernel inner field)) :=
  (composition_coordinate_hasSum outer inner inputCells field support output).tsum_eq

end Grad.RepresentedKernel.Composition
