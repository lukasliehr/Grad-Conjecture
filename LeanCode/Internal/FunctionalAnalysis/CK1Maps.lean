import RK1Algebra

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Grad.GenericCarriers
open scoped Topology

namespace Grad.RepresentedKernel.Composition

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  (outerMeasure : Measure Outer) (innerMeasure : Measure Inner)
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] (domain : Set Spatial)

omit [SigmaFinite outerMeasure] in
theorem inner_projection_quasi :
    QuasiMeasurePreserving (fun pair : (Outer × Inner) × Spatial => (pair.1.2, pair.2))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
      (innerMeasure.prod (volume.restrict domain)) :=
  quasiMeasurePreserving_snd.comp
    (measurePreserving_prodAssoc outerMeasure innerMeasure (volume.restrict domain)).quasiMeasurePreserving

theorem outer_projection_quasi :
    QuasiMeasurePreserving (fun pair : (Outer × Inner) × Spatial => (pair.1.1, pair.2))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
      (outerMeasure.prod (volume.restrict domain)) :=
  quasiMeasurePreserving_snd.comp
    ((measurePreserving_prodAssoc innerMeasure outerMeasure (volume.restrict domain)).comp
      ((measurePreserving_swap (μ := outerMeasure) (ν := innerMeasure)).prod
        (MeasurePreserving.id (volume.restrict domain)))).quasiMeasurePreserving

variable {outerMeasure innerMeasure domain}
  {inputDimension middleDimension outputDimension : ℕ}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def pairOrthogonal (parameter : Outer × Inner) : Spatial ≃ₗᵢ[ℝ] Spatial :=
  (outer.orthogonal parameter.1).trans (inner.orthogonal parameter.2)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem pairOrthogonal_invariant (parameter : Outer × Inner) :
    Grad.KernelPullback.Domain.Invariant domain (pairOrthogonal outer inner parameter) :=
  Grad.KernelPullback.Domain.invariant_trans domain _ _
    (outer.invariant parameter.1) (inner.invariant parameter.2)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem outer_action_measurable :
    Measurable (fun pair : (Outer × Inner) × Spatial => outer.orthogonal pair.1.1 pair.2) :=
  outer.actionMeasurable.comp (measurable_fst.fst.prodMk measurable_snd)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem pair_action_measurable :
    Measurable (fun pair : (Outer × Inner) × Spatial => pairOrthogonal outer inner pair.1 pair.2) :=
  inner.actionMeasurable.comp
    (measurable_fst.snd.prodMk (outer_action_measurable outer))

theorem outer_skew_preserving :
    MeasurePreserving
      (fun pair : (Outer × Inner) × Spatial => (pair.1, outer.orthogonal pair.1.1 pair.2))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain)) :=
  (MeasurePreserving.id (outerMeasure.prod innerMeasure)).skew_product
    (outer_action_measurable outer) (Filter.Eventually.of_forall fun parameter =>
      (Grad.KernelPullback.Domain.domainMeasurePreserving domain outer.domainMeasurable
        (outer.orthogonal parameter.1) (outer.invariant parameter.1)).map_eq)

theorem shifted_inner_projection_quasi :
    QuasiMeasurePreserving
      (fun pair : (Outer × Inner) × Spatial => (pair.1.2, outer.orthogonal pair.1.1 pair.2))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
      (innerMeasure.prod (volume.restrict domain)) :=
  (inner_projection_quasi outerMeasure innerMeasure domain).comp
    (outer_skew_preserving outer).quasiMeasurePreserving

def pairCoefficient (output middle input : ℤ) (pair : (Outer × Inner) × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  composedCoefficient outer.orthogonal outer.coefficient inner.coefficient output input
    (middle, pair.1.1, pair.1.2) pair.2

def pairWeight (output middle input : ℤ) (parameter : Outer × Inner) : ℝ :=
  outer.weight output middle parameter.1 * inner.weight middle input parameter.2

theorem pairCoefficient_measurable (output middle input : ℤ) :
    AEStronglyMeasurable (pairCoefficient outer inner output middle input)
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain)) :=
  (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
    (((outer.coefficientMeasurable output middle).comp_quasiMeasurePreserving
      (outer_projection_quasi outerMeasure innerMeasure domain)).prodMk
      ((inner.coefficientMeasurable middle input).comp_quasiMeasurePreserving
        (shifted_inner_projection_quasi outer)))

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem pairWeight_measurable (output middle input : ℤ) :
    Measurable (pairWeight outer inner output middle input) :=
  ((outer.weightMeasurable output middle).comp measurable_fst).mul
    ((inner.weightMeasurable middle input).comp measurable_snd)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem pairWeight_nonnegative (output middle input : ℤ) (parameter : Outer × Inner) :
    0 ≤ pairWeight outer inner output middle input parameter :=
  mul_nonneg (outer.weightNonnegative output middle parameter.1)
    (inner.weightNonnegative middle input parameter.2)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem pairWeight_integrable (output middle input : ℤ) :
    Integrable (pairWeight outer inner output middle input) (outerMeasure.prod innerMeasure) :=
  (outer.weightIntegrable output middle).mul_prod (inner.weightIntegrable middle input)

theorem pairWeight_integral (output middle input : ℤ) :
    (∫ parameter, pairWeight outer inner output middle input parameter
      ∂outerMeasure.prod innerMeasure) =
      (∫ parameter, outer.weight output middle parameter ∂outerMeasure) *
        ∫ parameter, inner.weight middle input parameter ∂innerMeasure :=
  integral_prod_mul _ _

theorem pairCoefficient_domination (output middle input : ℤ) :
    ∀ᵐ pair ∂(outerMeasure.prod innerMeasure).prod (volume.restrict domain),
      ‖pairCoefficient outer inner output middle input pair‖ ≤
        pairWeight outer inner output middle input pair.1 := by
  filter_upwards [(outer_projection_quasi outerMeasure innerMeasure domain).ae
      (outer.domination output middle),
    (shifted_inner_projection_quasi outer).ae (inner.domination middle input)]
    with pair outerBound innerBound
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul outerBound innerBound (norm_nonneg _)
      (outer.weightNonnegative output middle pair.1.1))

end Grad.RepresentedKernel.Composition
