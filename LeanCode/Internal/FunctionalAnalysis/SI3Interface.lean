import SI2Proof
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.SchurKernel.RealEnergy

def RealEnergyGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ℝ) (energy : Spatial → ℝ),
        Measurable weight → Measurable energy →
        (∀ parameter, 0 ≤ weight parameter) → (∀ point, 0 ≤ energy point) →
        Integrable weight measure → Integrable energy (volume.restrict domain) →
        Integrable (fun pair : Parameter × Spatial =>
          weight pair.1 * energy (orthogonal pair.1 pair.2))
          (measure.prod (volume.restrict domain)) ∧
        (∀ᵐ point ∂volume.restrict domain,
          Integrable (fun parameter => weight parameter * energy (orthogonal parameter point)) measure) ∧
        Integrable (fun point => ∫ parameter,
          weight parameter * energy (orthogonal parameter point) ∂measure) (volume.restrict domain) ∧
        (∫ point in domain, ∫ parameter,
          weight parameter * energy (orthogonal parameter point) ∂measure) =
          (∫ parameter, weight parameter ∂measure) * ∫ point in domain, energy point

def FieldEnergyGoal {Parameter Value : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Value] (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ℝ), Measurable weight →
        (∀ parameter, 0 ≤ weight parameter) → Integrable weight measure →
        ∀ field : Lp Value 2 (volume.restrict domain),
          Integrable (fun pair : Parameter × Spatial =>
            weight pair.1 * ‖field (orthogonal pair.1 pair.2)‖ ^ 2)
            (measure.prod (volume.restrict domain)) ∧
          (∀ᵐ point ∂volume.restrict domain,
            Integrable (fun parameter => weight parameter *
              ‖field (orthogonal parameter point)‖ ^ 2) measure) ∧
          Integrable (fun point => ∫ parameter,
            weight parameter * ‖field (orthogonal parameter point)‖ ^ 2 ∂measure)
            (volume.restrict domain) ∧
          (∫ point in domain, ∫ parameter,
            weight parameter * ‖field (orthogonal parameter point)‖ ^ 2 ∂measure) =
            (∫ parameter, weight parameter ∂measure) * ∫ point in domain, ‖field point‖ ^ 2

def PhysicalNormGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Invariant domain (orthogonal parameter)) →
      Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2) →
      ∀ (weight : Parameter → ℝ), Measurable weight →
        (∀ parameter, 0 ≤ weight parameter) → Integrable weight measure →
        ∀ field : Lp (EuclideanSpace ℂ (Fin dimension)) 2 (volume.restrict domain),
          (∫ point in domain, ∫ parameter,
            weight parameter * ‖field (orthogonal parameter point)‖ ^ 2 ∂measure) =
            (∫ parameter, weight parameter ∂measure) * ‖field‖ ^ 2

end Grad.SchurKernel.RealEnergy

#check hasFiniteIntegral_iff_ofReal
#check ENNReal.ofReal_mul
#check ofReal_integral_eq_lintegral_ofReal
#check integral_eq_lintegral_of_nonneg_ae
#check integrable_prod_iff'
#check Integrable.integral_prod_right
#check integral_prod_symm
#check Lp.stronglyMeasurable
#check MemLp.integrable_sq
#check StronglyMeasurable.norm
#check Measurable.pow_const
#check L2.inner_def

section
variable {Value : Type*} [NormedAddCommGroup Value] (domain : Set Spatial)
  (field : Lp Value 2 (volume.restrict domain))
#check ((Lp.stronglyMeasurable field).norm.measurable.pow_const 2 :
  Measurable (fun point => ‖field point‖ ^ 2))
#check ((Lp.memLp field).norm.integrable_sq :
  Integrable (fun point => ‖field point‖ ^ 2) (volume.restrict domain))
end
