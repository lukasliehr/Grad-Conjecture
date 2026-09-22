import DP1DomainInterface
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.SchurKernel.Energy

def ProductEnergyGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ENNReal) (energy : Spatial → ENNReal),
        Measurable weight → Measurable energy →
        (∫⁻ pair : Parameter × Spatial, weight pair.1 * energy (orthogonal pair.1 pair.2)
          ∂measure.prod ((volume : Measure Spatial).restrict domain)) =
          (∫⁻ parameter, weight parameter ∂measure) * ∫⁻ point in domain, energy point

def SwappedEnergyGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ENNReal) (energy : Spatial → ENNReal),
        Measurable weight → Measurable energy →
        (∫⁻ point in domain, ∫⁻ parameter,
          weight parameter * energy (orthogonal parameter point) ∂measure) =
          (∫⁻ parameter, weight parameter ∂measure) * ∫⁻ point in domain, energy point

def FiniteEnergyGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ENNReal) (energy : Spatial → ENNReal),
        Measurable weight → Measurable energy →
        (∫⁻ parameter, weight parameter ∂measure) < ⊤ →
        (∫⁻ point in domain, energy point) < ⊤ →
        (∫⁻ point in domain, ∫⁻ parameter,
          weight parameter * energy (orthogonal parameter point) ∂measure) < ⊤ ∧
        ∀ᵐ point ∂((volume : Measure Spatial).restrict domain),
          (∫⁻ parameter, weight parameter * energy (orthogonal parameter point) ∂measure) < ⊤

end Grad.SchurKernel.Energy

#check MeasureTheory.lintegral_prod
#check MeasureTheory.lintegral_prod_symm
#check MeasureTheory.lintegral_const_mul
#check MeasureTheory.lintegral_mul_const
#check MeasureTheory.MeasurePreserving.lintegral_comp
#check Measurable.lintegral_prod_left'
#check MeasureTheory.ae_lt_top
#check ENNReal.mul_lt_top
#check (inferInstance : SigmaFinite ((volume : Measure Spatial).restrict (Set.univ : Set Spatial)))
