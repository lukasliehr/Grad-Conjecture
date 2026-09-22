import CK1Maps

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Grad.GenericCarriers
open scoped Topology

namespace Grad.RepresentedKernel.Composition

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def pairOperator (output middle input : ℤ) :
    DomainL2 (PhysicalValue inputDimension) domain →L[ℂ] DomainL2 (PhysicalValue outputDimension) domain :=
  Grad.KernelIntegral.integralKernelCLM (outerMeasure.prod innerMeasure) outer.domainMeasurable
    (pairOrthogonal outer inner) (pairOrthogonal_invariant outer inner)
    (pair_action_measurable outer inner) (pairCoefficient outer inner output middle input)
    (pairWeight outer inner output middle input) (pairCoefficient_measurable outer inner output middle input)
    (pairWeight_measurable outer inner output middle input) (pairWeight_nonnegative outer inner output middle input)
    (pairWeight_integrable outer inner output middle input) (pairCoefficient_domination outer inner output middle input)

theorem pairOperator_ae (output middle input : ℤ) (field : DomainL2 (PhysicalValue inputDimension) domain) :
    ∀ᵐ point ∂volume.restrict domain, pairOperator outer inner output middle input field point =
      ∫ parameter, pairCoefficient outer inner output middle input (parameter, point)
        (field (pairOrthogonal outer inner parameter point)) ∂outerMeasure.prod innerMeasure :=
  Grad.KernelIntegral.integralKernelCLM_apply_ae (outerMeasure.prod innerMeasure) outer.domainMeasurable
    (pairOrthogonal outer inner) (pairOrthogonal_invariant outer inner)
    (pair_action_measurable outer inner) (pairCoefficient outer inner output middle input)
    (pairWeight outer inner output middle input) (pairCoefficient_measurable outer inner output middle input)
    (pairWeight_measurable outer inner output middle input) (pairWeight_nonnegative outer inner output middle input)
    (pairWeight_integrable outer inner output middle input) (pairCoefficient_domination outer inner output middle input)
    field

theorem pairOperator_integrable (output middle input : ℤ)
    (field : DomainL2 (PhysicalValue inputDimension) domain) :
    ∀ᵐ point ∂volume.restrict domain, Integrable
      (fun parameter => pairCoefficient outer inner output middle input (parameter, point)
        (field (pairOrthogonal outer inner parameter point))) (outerMeasure.prod innerMeasure) :=
  (Grad.KernelIntegral.row_integrable_and_sq_bound (outerMeasure.prod innerMeasure) outer.domainMeasurable
    (pairOrthogonal outer inner) (pairOrthogonal_invariant outer inner)
    (pair_action_measurable outer inner) (pairCoefficient outer inner output middle input)
    (pairWeight outer inner output middle input) (pairCoefficient_measurable outer inner output middle input)
    (pairWeight_measurable outer inner output middle input) (pairWeight_nonnegative outer inner output middle input)
    (pairWeight_integrable outer inner output middle input) (pairCoefficient_domination outer inner output middle input)
    field).mono fun _ properties => properties.1

theorem pairOperator_norm_le (output middle input : ℤ) :
    ‖pairOperator outer inner output middle input‖ ≤
      (∫ parameter, outer.weight output middle parameter ∂outerMeasure) *
        ∫ parameter, inner.weight middle input parameter ∂innerMeasure := by
  rw [← pairWeight_integral outer inner output middle input]
  exact Grad.KernelIntegral.integralKernelCLM_norm_le (outerMeasure.prod innerMeasure) outer.domainMeasurable
    (pairOrthogonal outer inner) (pairOrthogonal_invariant outer inner)
    (pair_action_measurable outer inner) (pairCoefficient outer inner output middle input)
    (pairWeight outer inner output middle input) (pairCoefficient_measurable outer inner output middle input)
    (pairWeight_measurable outer inner output middle input) (pairWeight_nonnegative outer inner output middle input)
    (pairWeight_integrable outer inner output middle input) (pairCoefficient_domination outer inner output middle input)

section Entry

variable {Parameter : Type*} [MeasurableSpace Parameter] {measure : Measure Parameter} [SigmaFinite measure]
  {sourceDimension targetDimension : ℕ}
  (data : Grad.FullCellKernel.L2KernelData measure sourceDimension targetDimension domain)

theorem entry_ae (output input : ℤ) (field : DomainL2 (PhysicalValue sourceDimension) domain) :
    ∀ᵐ point ∂volume.restrict domain, Grad.FullCellKernel.entry data output input field point =
      ∫ parameter, data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point)) ∂measure :=
  Grad.KernelIntegral.integralKernelCLM_apply_ae measure data.domainMeasurable
    data.orthogonal data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
    (data.coefficientMeasurable output input) (data.weightMeasurable output input)
    (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input) field

theorem entry_integrable (output input : ℤ) (field : DomainL2 (PhysicalValue sourceDimension) domain) :
    ∀ᵐ point ∂volume.restrict domain, Integrable
      (fun parameter => data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point))) measure :=
  (Grad.KernelIntegral.row_integrable_and_sq_bound measure data.domainMeasurable
    data.orthogonal data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
    (data.coefficientMeasurable output input) (data.weightMeasurable output input)
    (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input)
    field).mono fun _ properties => properties.1

end Entry

theorem pairOperator_composition (output middle input : ℤ) :
    pairOperator outer inner output middle input =
      (Grad.FullCellKernel.entry outer output middle).comp (Grad.FullCellKernel.entry inner middle input) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  have represented := Grad.KernelIntegral.transported_ae_eq_sections outerMeasure outer.domainMeasurable
    outer.orthogonal outer.invariant outer.actionMeasurable (entry_ae inner middle input field)
  have integrableInside : ∀ᵐ point ∂volume.restrict domain, ∀ᵐ parameter ∂outerMeasure,
      Integrable (fun innerParameter => inner.coefficient middle input
        (innerParameter, outer.orthogonal parameter point)
        (field (inner.orthogonal innerParameter (outer.orthogonal parameter point)))) innerMeasure :=
    ae_ae_of_ae_prod
      ((measurePreserving_swap (μ := volume.restrict domain) (ν := outerMeasure)).quasiMeasurePreserving.ae
        ((Grad.KernelIntegral.joint_action_quasiMeasurePreserving outerMeasure outer.domainMeasurable
          outer.orthogonal outer.invariant outer.actionMeasurable).ae (entry_integrable inner middle input field)))
  filter_upwards [pairOperator_ae outer inner output middle input field,
    entry_ae outer output middle (Grad.FullCellKernel.entry inner middle input field),
    pairOperator_integrable outer inner output middle input field, represented, integrableInside]
    with point pairLiteral compositeLiteral integrablePair inside insideIntegrable
  change pairOperator outer inner output middle input field point =
    Grad.FullCellKernel.entry outer output middle (Grad.FullCellKernel.entry inner middle input field) point
  rw [pairLiteral, compositeLiteral, integral_prod _ integrablePair]
  apply integral_congr_ae
  filter_upwards [inside, insideIntegrable] with parameter innerLiteral innerIntegrability
  rw [innerLiteral]
  change (∫ innerParameter, outer.coefficient output middle (parameter, point)
      (inner.coefficient middle input (innerParameter, outer.orthogonal parameter point)
        (field (inner.orthogonal innerParameter (outer.orthogonal parameter point)))) ∂innerMeasure) =
    outer.coefficient output middle (parameter, point)
      (∫ innerParameter, inner.coefficient middle input (innerParameter, outer.orthogonal parameter point)
        (field (inner.orthogonal innerParameter (outer.orthogonal parameter point))) ∂innerMeasure)
  exact (outer.coefficient output middle (parameter, point)).integral_comp_comm innerIntegrability

end Grad.RepresentedKernel.Composition
