import SI1Proof
import SI3Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.KernelIntegral

def integralAction {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (coefficient : Parameter × Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
    (point : Spatial) : EuclideanSpace ℂ (Fin outputDimension) :=
  ∫ parameter, coefficient (parameter, point) (representative (orthogonal parameter point)) ∂measure

def kernelSpec {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension : ℕ) (domain : Set Spatial)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (coefficient : Parameter × Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    (weight : Parameter → ℝ)
    (kernel : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain)) : Prop :=
  (∀ field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain),
    (∀ᵐ point ∂volume.restrict domain,
      Integrable (fun parameter => coefficient (parameter, point)
        (field (orthogonal parameter point))) measure) ∧
    MemLp (integralAction measure inputDimension outputDimension orthogonal coefficient field)
      2 (volume.restrict domain)) ∧
  ‖kernel‖ ≤ (∫ parameter, weight parameter ∂measure) ∧
  (∀ field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain),
    ∀ᵐ point ∂volume.restrict domain, kernel field point =
      ∫ parameter, coefficient (parameter, point) (field (orthogonal parameter point)) ∂measure) ∧
  (∀ field, ‖kernel field‖ ^ 2 ≤ (∫ parameter, weight parameter ∂measure) ^ 2 * ‖field‖ ^ 2) ∧
  (∀ field, ‖kernel field‖ ≤ (∫ parameter, weight parameter ∂measure) * ‖field‖) ∧
  (∀ (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
      (membership : MemLp representative 2 (volume.restrict domain)),
    ∀ᵐ point ∂volume.restrict domain, kernel (membership.toLp representative) point =
      ∫ parameter, coefficient (parameter, point)
        (representative (orthogonal parameter point)) ∂measure) ∧
  (∀ (first second : Spatial → EuclideanSpace ℂ (Fin inputDimension))
      (firstMembership : MemLp first 2 (volume.restrict domain))
      (secondMembership : MemLp second 2 (volume.restrict domain)),
    first =ᵐ[volume.restrict domain] second →
      kernel (firstMembership.toLp first) = kernel (secondMembership.toLp second)) ∧
  (∀ first second, kernel (first + second) = kernel first + kernel second) ∧
  (∀ (scalar : ℂ) field, kernel (scalar • field) = scalar • kernel field)

def blockGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (inputDimension outputDimension : ℕ) (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (coefficient : Parameter × Spatial →
          EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
        (weight : Parameter → ℝ),
        AEStronglyMeasurable coefficient (measure.prod (volume.restrict domain)) →
        Measurable weight → (∀ parameter, 0 ≤ weight parameter) → Integrable weight measure →
        (∀ᵐ pair ∂measure.prod (volume.restrict domain), ‖coefficient pair‖ ≤ weight pair.1) →
        ∃ kernel : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →L[ℂ]
          Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain),
          kernelSpec measure inputDimension outputDimension domain orthogonal coefficient weight kernel

def physicalConsumerGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (inputDimension outputDimension : ℕ) (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (coefficient : Parameter × Spatial →
          EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
        (weight : Parameter → ℝ),
        AEStronglyMeasurable coefficient (measure.prod (volume.restrict domain)) →
        Measurable weight → (∀ parameter, 0 ≤ weight parameter) → Integrable weight measure →
        (∀ᵐ pair ∂measure.prod (volume.restrict domain), ‖coefficient pair‖ ≤ weight pair.1) →
        ∃ kernel : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →L[ℂ]
          Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain),
          (∀ field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain),
            (∀ᵐ point ∂volume.restrict domain,
              Integrable (fun parameter => coefficient (parameter, point)
                (field (orthogonal parameter point))) measure) ∧
            MemLp (fun point => ∫ parameter, coefficient (parameter, point)
              (field (orthogonal parameter point)) ∂measure) 2 (volume.restrict domain)) ∧
          ‖kernel‖ ≤ (∫ parameter, weight parameter ∂measure) ∧
          (∀ field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain),
            ∀ᵐ point ∂volume.restrict domain, kernel field point =
              ∫ parameter, coefficient (parameter, point)
                (field (orthogonal parameter point)) ∂measure) ∧
          (∀ field, ‖kernel field‖ ^ 2 ≤ (∫ parameter, weight parameter ∂measure) ^ 2 * ‖field‖ ^ 2) ∧
          (∀ field, ‖kernel field‖ ≤ (∫ parameter, weight parameter ∂measure) * ‖field‖) ∧
          (∀ (representative : Spatial → EuclideanSpace ℂ (Fin inputDimension))
              (membership : MemLp representative 2 (volume.restrict domain)),
            ∀ᵐ point ∂volume.restrict domain, kernel (membership.toLp representative) point =
              ∫ parameter, coefficient (parameter, point)
                (representative (orthogonal parameter point)) ∂measure) ∧
          (∀ (first second : Spatial → EuclideanSpace ℂ (Fin inputDimension))
              (firstMembership : MemLp first 2 (volume.restrict domain))
              (secondMembership : MemLp second 2 (volume.restrict domain)),
            first =ᵐ[volume.restrict domain] second →
              kernel (firstMembership.toLp first) = kernel (secondMembership.toLp second)) ∧
          (∀ first second, kernel (first + second) = kernel first + kernel second) ∧
          (∀ (scalar : ℂ) field, kernel (scalar • field) = scalar • kernel field)

end Grad.KernelIntegral
