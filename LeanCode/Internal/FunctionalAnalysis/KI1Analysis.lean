import KI1Interface

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.KernelIntegral

variable {Parameter : Type*} [MeasurableSpace Parameter]

theorem joint_action_quasiMeasurePreserving (measure : Measure Parameter) [SigmaFinite measure]
    {domain : Set Spatial} (domainMeasurable : MeasurableSet domain)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Invariant domain (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2)) :
    QuasiMeasurePreserving (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2)
      (measure.prod (volume.restrict domain)) (volume.restrict domain) :=
  (quasiMeasurePreserving_snd (μ := measure) (ν := volume.restrict domain)).comp
    ((MeasurePreserving.id measure).skew_product actionMeasurable
      (Filter.Eventually.of_forall fun parameter =>
        (domainMeasurePreserving domain domainMeasurable (orthogonal parameter)
          (invariant parameter)).map_eq)).quasiMeasurePreserving

theorem transported_ae_eq_sections (measure : Measure Parameter) [SigmaFinite measure]
    {domain : Set Spatial} (domainMeasurable : MeasurableSet domain)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Invariant domain (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    {Value : Type*} {first second : Spatial → Value}
    (equality : first =ᵐ[volume.restrict domain] second) :
    ∀ᵐ point ∂volume.restrict domain, ∀ᵐ parameter ∂measure,
      first (orthogonal parameter point) = second (orthogonal parameter point) :=
  ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := volume.restrict domain) (ν := measure)).quasiMeasurePreserving.ae
      ((joint_action_quasiMeasurePreserving measure domainMeasurable orthogonal invariant
        actionMeasurable).ae_eq equality))

theorem integralAction_congr_ae (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (domainMeasurable : MeasurableSet domain)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Invariant domain (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter × Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    {first second : Spatial → EuclideanSpace ℂ (Fin inputDimension)}
    (equality : first =ᵐ[volume.restrict domain] second) :
    integralAction measure inputDimension outputDimension orthogonal coefficient first =ᵐ[volume.restrict domain]
      integralAction measure inputDimension outputDimension orthogonal coefficient second := by
  filter_upwards [transported_ae_eq_sections measure domainMeasurable orthogonal invariant
    actionMeasurable equality] with point rowEquality
  apply integral_congr_ae
  filter_upwards [rowEquality] with parameter equalityAt
  rw [equalityAt]

theorem integralAction_aestronglyMeasurable (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter × Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    (coefficientMeasurable : AEStronglyMeasurable coefficient (measure.prod (volume.restrict domain)))
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    AEStronglyMeasurable (integralAction measure inputDimension outputDimension orthogonal coefficient field)
      (volume.restrict domain) := by
  have integrandMeasurable : AEStronglyMeasurable
      (fun pair : Parameter × Spatial => coefficient pair (field (orthogonal pair.1 pair.2)))
      (measure.prod (volume.restrict domain)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (coefficientMeasurable.prodMk
        ((Lp.stronglyMeasurable field).comp_measurable actionMeasurable).aestronglyMeasurable)
  exact integrandMeasurable.prod_swap.integral_prod_right'

section Estimates

variable (measure : Measure Parameter) [SigmaFinite measure]
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
  (domination : ∀ᵐ pair ∂measure.prod (volume.restrict domain), ‖coefficient pair‖ ≤ weight pair.1)

include domainMeasurable invariant actionMeasurable coefficientMeasurable
  weightMeasurable weightNonnegative weightIntegrable domination

theorem row_integrable_and_sq_bound
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      Integrable (fun parameter => coefficient (parameter, point)
        (field (orthogonal parameter point))) measure ∧
      ‖integralAction measure inputDimension outputDimension orthogonal coefficient field point‖ ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) *
          ∫ parameter, weight parameter * ‖field (orthogonal parameter point)‖ ^ 2 ∂measure := by
  have energy := SchurKernel.RealEnergy.field_energy measure domain domainMeasurable orthogonal
    invariant actionMeasurable weight weightMeasurable weightNonnegative weightIntegrable field
  have rowDomination : ∀ᵐ point ∂volume.restrict domain, ∀ᵐ parameter ∂measure,
      ‖coefficient (parameter, point)‖ ≤ weight parameter :=
    ae_ae_of_ae_prod
      ((measurePreserving_swap (μ := volume.restrict domain) (ν := measure)).quasiMeasurePreserving.ae
        domination)
  filter_upwards [coefficientMeasurable.prodMk_right, energy.2.1, rowDomination]
    with point rowMeasurable rowEnergy rowEstimate
  exact SchurKernel.Integral.coefficient_row measure inputDimension outputDimension
    (fun parameter => coefficient (parameter, point)) (fun parameter => field (orthogonal parameter point))
    weight (Filter.Eventually.of_forall weightNonnegative) rowMeasurable
    ((Lp.stronglyMeasurable field).comp_measurable
      (actionMeasurable.comp measurable_prodMk_right)).aestronglyMeasurable
    weightIntegrable rowEnergy rowEstimate

theorem integralAction_memLp
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    MemLp (integralAction measure inputDimension outputDimension orthogonal coefficient field)
      2 (volume.restrict domain) := by
  have outputMeasurable := integralAction_aestronglyMeasurable measure orthogonal actionMeasurable
    coefficient coefficientMeasurable field
  apply (memLp_two_iff_integrable_sq_norm outputMeasurable).2
  have energy := SchurKernel.RealEnergy.field_energy measure domain domainMeasurable orthogonal
    invariant actionMeasurable weight weightMeasurable weightNonnegative weightIntegrable field
  refine (energy.2.2.1.const_mul (∫ parameter, weight parameter ∂measure)).mono'
    (outputMeasurable.norm.pow 2) ?_
  filter_upwards [row_integrable_and_sq_bound measure domainMeasurable orthogonal invariant
    actionMeasurable coefficient weight coefficientMeasurable weightMeasurable weightNonnegative
    weightIntegrable domination field] with point rowBound
  simpa only [norm_pow, norm_norm] using rowBound.2

theorem integralAction_integral_sq_le
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    (∫ point, ‖integralAction measure inputDimension outputDimension orthogonal coefficient field point‖ ^ 2
      ∂volume.restrict domain) ≤ (∫ parameter, weight parameter ∂measure) ^ 2 * ‖field‖ ^ 2 := by
  have membership := integralAction_memLp measure domainMeasurable orthogonal invariant actionMeasurable
    coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field
  have energy := SchurKernel.RealEnergy.field_energy measure domain domainMeasurable orthogonal
    invariant actionMeasurable weight weightMeasurable weightNonnegative weightIntegrable field
  have estimate := integral_mono_ae membership.norm.integrable_sq
    (energy.2.2.1.const_mul (∫ parameter, weight parameter ∂measure))
    ((row_integrable_and_sq_bound measure domainMeasurable orthogonal invariant actionMeasurable
      coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
      domination field).mono fun _ rowBound => rowBound.2)
  rw [integral_const_mul, SchurKernel.RealEnergy.physical_norm measure inputDimension domain
    domainMeasurable orthogonal invariant actionMeasurable weight weightMeasurable weightNonnegative
    weightIntegrable field] at estimate
  simpa only [pow_two, mul_assoc] using estimate

end Estimates
end Grad.KernelIntegral
