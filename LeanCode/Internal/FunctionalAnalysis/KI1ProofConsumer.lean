import KI1Construction

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.KernelIntegral

theorem integralKernelCLM_spec {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (domainMeasurable : MeasurableSet domain)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Invariant domain (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter × Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    (weight : Parameter → ℝ)
    (coefficientMeasurable : AEStronglyMeasurable coefficient (measure.prod (volume.restrict domain)))
    (weightMeasurable : Measurable weight) (weightNonnegative : ∀ parameter, 0 ≤ weight parameter)
    (weightIntegrable : Integrable weight measure)
    (domination : ∀ᵐ pair ∂measure.prod (volume.restrict domain), ‖coefficient pair‖ ≤ weight pair.1) :
    kernelSpec measure inputDimension outputDimension domain orthogonal coefficient weight
      (integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination) := by
  refine ⟨?_, integralKernelCLM_norm_le measure domainMeasurable orthogonal invariant actionMeasurable
    coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_norm_sq_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_norm_apply_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_toLp_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_representative_independent measure domainMeasurable orthogonal invariant actionMeasurable
      coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_add measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_smul measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination⟩
  intro field
  exact ⟨(row_integrable_and_sq_bound measure domainMeasurable orthogonal invariant actionMeasurable
    coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
    field).mono fun _ rowBound => rowBound.1,
    integralAction_memLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field⟩

theorem blockConsumer {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : blockGoal measure := by
  intro inputDimension outputDimension domain domainMeasurable orthogonal invariant actionMeasurable
    coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
  exact ⟨integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination,
    integralKernelCLM_spec measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination⟩

theorem physicalConsumer {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : physicalConsumerGoal measure :=
  blockConsumer measure

end Grad.KernelIntegral
