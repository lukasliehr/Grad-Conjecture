import KI1Analysis

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.KernelIntegral

variable {Parameter : Type*} [MeasurableSpace Parameter]
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
  (domination : ∀ᵐ pair ∂measure.prod (volume.restrict domain), ‖coefficient pair‖ ≤ weight pair.1)

def integralActionLp
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain) :=
  (integralAction_memLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field).toLp
      (integralAction measure inputDimension outputDimension orthogonal coefficient field)

theorem integralActionLp_apply_ae
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field point =
          integralAction measure inputDimension outputDimension orthogonal coefficient field point :=
  (integralAction_memLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field).coeFn_toLp

theorem integralActionLp_norm_sq_le
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ‖integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field‖ ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) ^ 2 * ‖field‖ ^ 2 := by
  rw [SchurKernel.RealEnergy.realLp_norm_sq]
  calc
    _ = ∫ point, ‖integralAction measure inputDimension outputDimension orthogonal coefficient field point‖ ^ 2
        ∂volume.restrict domain := by
      apply integral_congr_ae
      filter_upwards [integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable
        coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
        domination field] with point literal
      rw [literal]
    _ ≤ _ := integralAction_integral_sq_le measure domainMeasurable orthogonal invariant actionMeasurable
      coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field

theorem integralActionLp_norm_le
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ‖integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field‖ ≤
        (∫ parameter, weight parameter ∂measure) * ‖field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (integral_nonneg weightNonnegative) (norm_nonneg _))).mp
  simpa only [mul_pow] using integralActionLp_norm_sq_le measure domainMeasurable orthogonal invariant
    actionMeasurable coefficient weight coefficientMeasurable weightMeasurable weightNonnegative
    weightIntegrable domination field

theorem integralActionLp_add
    (first second : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination (first + second) =
      integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination first +
      integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination second := by
  apply Lp.ext
  filter_upwards [integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable
      coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
      domination (first + second),
    integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination first,
    integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination second,
    integralAction_congr_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient
      (Lp.coeFn_add first second),
    row_integrable_and_sq_bound measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination first,
    row_integrable_and_sq_bound measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination second,
    Lp.coeFn_add
      (integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination first)
      (integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination second)]
    with point literal firstLiteral secondLiteral inputAddition firstRow secondRow outputAddition
  simp only [Pi.add_apply] at outputAddition
  rw [literal, inputAddition, outputAddition, firstLiteral, secondLiteral]
  simp only [integralAction, Pi.add_apply, map_add]
  exact integral_add firstRow.1 secondRow.1

theorem integralActionLp_smul (scalar : ℂ)
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination (scalar • field) =
      scalar • integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field := by
  apply Lp.ext
  filter_upwards [integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable
      coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
      domination (scalar • field),
    integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field,
    integralAction_congr_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient
      (Lp.coeFn_smul scalar field),
    Lp.coeFn_smul scalar
      (integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field)]
    with point literal fieldLiteral inputScalar outputScalar
  simp only [Pi.smul_apply] at outputScalar
  rw [literal, inputScalar, outputScalar, fieldLiteral]
  simp only [integralAction, Pi.smul_apply, map_smul, integral_smul]

def integralKernelLinear :
    Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →ₗ[ℂ]
      Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain) where
  toFun := integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
  map_add' := integralActionLp_add measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
  map_smul' := integralActionLp_smul measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination

def integralKernelCLM :
    Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain) :=
  (integralKernelLinear measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination).mkContinuous
      (∫ parameter, weight parameter ∂measure)
      (integralActionLp_norm_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination)

theorem integralKernelCLM_apply
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field =
      integralActionLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field := rfl

theorem integralKernelCLM_apply_ae
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field point =
        ∫ parameter, coefficient (parameter, point) (field (orthogonal parameter point)) ∂measure :=
  integralActionLp_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field

theorem integralKernelCLM_norm_sq_le
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ‖integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field‖ ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) ^ 2 * ‖field‖ ^ 2 :=
  integralActionLp_norm_sq_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field

theorem integralKernelCLM_norm_apply_le
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    ‖integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field‖ ≤
        (∫ parameter, weight parameter ∂measure) * ‖field‖ :=
  integralActionLp_norm_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field

theorem integralKernelCLM_norm_le :
    ‖integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination‖ ≤
        ∫ parameter, weight parameter ∂measure :=
  (integralKernelLinear measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination).mkContinuous_norm_le
      (integral_nonneg weightNonnegative)
      (integralActionLp_norm_le measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination)

theorem integralKernelCLM_toLp_ae
    (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
    (membership : MemLp representative 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
        (membership.toLp representative) point =
        ∫ parameter, coefficient (parameter, point) (representative (orthogonal parameter point)) ∂measure :=
  Filter.EventuallyEq.trans
    (integralKernelCLM_apply_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
      (membership.toLp representative))
      (integralAction_congr_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient
        membership.coeFn_toLp)

include domainMeasurable invariant actionMeasurable coefficientMeasurable
  weightMeasurable weightNonnegative weightIntegrable domination in
theorem integralAction_representative_memLp
    (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
    (membership : MemLp representative 2 (volume.restrict domain)) :
    MemLp (integralAction measure inputDimension outputDimension orthogonal coefficient representative)
      2 (volume.restrict domain) :=
  (memLp_congr_ae (integralAction_congr_ae measure domainMeasurable orthogonal invariant actionMeasurable
    coefficient membership.coeFn_toLp)).mp
      (integralAction_memLp measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
        (membership.toLp representative))

theorem integralKernelCLM_toLp
    (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
    (membership : MemLp representative 2 (volume.restrict domain)) :
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
      (membership.toLp representative) =
      (integralAction_representative_memLp measure domainMeasurable orthogonal invariant actionMeasurable
        coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
        domination representative membership).toLp
        (integralAction measure inputDimension outputDimension orthogonal coefficient representative) := by
  apply Lp.ext
  exact Filter.EventuallyEq.trans
    (integralKernelCLM_toLp_ae measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
      representative membership)
      (integralAction_representative_memLp measure domainMeasurable orthogonal invariant actionMeasurable
        coefficient weight coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable
        domination representative membership).coeFn_toLp.symm

theorem integralKernelCLM_representative_independent
    (first second : Spatial → EuclideanSpace ℂ (Fin inputDimension))
    (firstMembership : MemLp first 2 (volume.restrict domain))
    (secondMembership : MemLp second 2 (volume.restrict domain))
    (equality : first =ᵐ[volume.restrict domain] second) :
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
      (firstMembership.toLp first) =
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination
      (secondMembership.toLp second) :=
  congrArg (integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
    coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination)
    (MemLp.toLp_congr firstMembership secondMembership equality)

theorem integralKernelCLM_add
    (first second : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination (first + second) =
      integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination first +
      integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination second :=
  map_add _ _ _

theorem integralKernelCLM_smul (scalar : ℂ)
    (field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain)) :
    integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
      coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination (scalar • field) =
      scalar • integralKernelCLM measure domainMeasurable orthogonal invariant actionMeasurable coefficient weight
        coefficientMeasurable weightMeasurable weightNonnegative weightIntegrable domination field :=
  map_smul _ _ _

end Grad.KernelIntegral
