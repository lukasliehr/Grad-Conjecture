import SI3Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.SchurKernel.RealEnergy

section Generic

variable {Parameter Space : Type*} [MeasurableSpace Parameter] [MeasurableSpace Space]
  (parameterMeasure : Measure Parameter) (spatialMeasure : Measure Space)
  [SFinite parameterMeasure] [SFinite spatialMeasure]
  (action : Parameter → Space → Space)
  (actionMeasurable : Measurable (fun pair : Parameter × Space => action pair.1 pair.2))
  (preserving : ∀ parameter, MeasurePreserving (action parameter) spatialMeasure spatialMeasure)
  (weight : Parameter → ℝ) (energy : Space → ℝ)
  (weightMeasurable : Measurable weight) (energyMeasurable : Measurable energy)
  (weightNonnegative : ∀ parameter, 0 ≤ weight parameter)
  (energyNonnegative : ∀ point, 0 ≤ energy point)
  (weightIntegrable : Integrable weight parameterMeasure)
  (energyIntegrable : Integrable energy spatialMeasure)

include actionMeasurable preserving weightMeasurable energyMeasurable
  weightNonnegative energyNonnegative weightIntegrable energyIntegrable

theorem ofReal_product_energy :
    (∫⁻ pair : Parameter × Space,
      ENNReal.ofReal (weight pair.1 * energy (action pair.1 pair.2))
      ∂parameterMeasure.prod spatialMeasure) =
      ENNReal.ofReal (∫ parameter, weight parameter ∂parameterMeasure) *
        ENNReal.ofReal (∫ point, energy point ∂spatialMeasure) := by
  have integrandLaw : (fun pair : Parameter × Space =>
      ENNReal.ofReal (weight pair.1 * energy (action pair.1 pair.2))) =
      fun pair => ENNReal.ofReal (weight pair.1) *
        ENNReal.ofReal (energy (action pair.1 pair.2)) := by
    funext pair
    exact ENNReal.ofReal_mul (weightNonnegative pair.1)
  rw [integrandLaw, Energy.product_energy_of_measurePreserving
    parameterMeasure spatialMeasure action actionMeasurable preserving
    (fun parameter => ENNReal.ofReal (weight parameter))
    (fun point => ENNReal.ofReal (energy point))
    weightMeasurable.ennreal_ofReal energyMeasurable.ennreal_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal weightIntegrable
      (Filter.Eventually.of_forall weightNonnegative),
    ← ofReal_integral_eq_lintegral_ofReal energyIntegrable
      (Filter.Eventually.of_forall energyNonnegative)]

theorem transport_integrability_and_integral :
    Integrable (fun pair : Parameter × Space =>
      weight pair.1 * energy (action pair.1 pair.2)) (parameterMeasure.prod spatialMeasure) ∧
    (∀ᵐ point ∂spatialMeasure,
      Integrable (fun parameter => weight parameter * energy (action parameter point))
        parameterMeasure) ∧
    Integrable (fun point => ∫ parameter,
      weight parameter * energy (action parameter point) ∂parameterMeasure) spatialMeasure ∧
    (∫ point, ∫ parameter, weight parameter * energy (action parameter point)
      ∂parameterMeasure ∂spatialMeasure) =
      (∫ parameter, weight parameter ∂parameterMeasure) * ∫ point, energy point ∂spatialMeasure := by
  have integrandMeasurable : Measurable (fun pair : Parameter × Space =>
      weight pair.1 * energy (action pair.1 pair.2)) :=
    (weightMeasurable.comp measurable_fst).mul (energyMeasurable.comp actionMeasurable)
  have integrandNonnegative : ∀ pair : Parameter × Space,
      0 ≤ weight pair.1 * energy (action pair.1 pair.2) :=
    fun pair => mul_nonneg (weightNonnegative pair.1) (energyNonnegative _)
  have energyIdentity := ofReal_product_energy parameterMeasure spatialMeasure action
    actionMeasurable preserving weight energy weightMeasurable energyMeasurable
    weightNonnegative energyNonnegative weightIntegrable energyIntegrable
  have productIntegrable : Integrable (fun pair : Parameter × Space =>
      weight pair.1 * energy (action pair.1 pair.2)) (parameterMeasure.prod spatialMeasure) := by
    refine ⟨integrandMeasurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall integrandNonnegative)).2 ?_⟩
    rw [energyIdentity]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨productIntegrable, productIntegrable.prod_left_ae,
    productIntegrable.integral_prod_right, ?_⟩
  calc
    _ = ∫ pair : Parameter × Space, weight pair.1 * energy (action pair.1 pair.2)
        ∂parameterMeasure.prod spatialMeasure := (integral_prod_symm _ productIntegrable).symm
    _ = (∫⁻ pair : Parameter × Space,
        ENNReal.ofReal (weight pair.1 * energy (action pair.1 pair.2))
        ∂parameterMeasure.prod spatialMeasure).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall integrandNonnegative)
        integrandMeasurable.aestronglyMeasurable
    _ = _ := by
      rw [energyIdentity, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (integral_nonneg weightNonnegative),
        ENNReal.toReal_ofReal (integral_nonneg energyNonnegative)]

end Generic

theorem real_energy {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : RealEnergyGoal measure := by
  intro domain domainMeasurable orthogonal invariant actionMeasurable
    weight energy weightMeasurable energyMeasurable weightNonnegative energyNonnegative
    weightIntegrable energyIntegrable
  exact transport_integrability_and_integral measure (volume.restrict domain)
    (fun parameter => orthogonal parameter) actionMeasurable
    (fun parameter => domainMeasurePreserving domain domainMeasurable
      (orthogonal parameter) (invariant parameter)) weight energy weightMeasurable energyMeasurable
    weightNonnegative energyNonnegative weightIntegrable energyIntegrable

theorem field_energy {Parameter Value : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Value] (measure : Measure Parameter) [SigmaFinite measure] :
    FieldEnergyGoal (Value := Value) measure := by
  intro domain domainMeasurable orthogonal invariant actionMeasurable
    weight weightMeasurable weightNonnegative weightIntegrable field
  exact real_energy measure domain domainMeasurable orthogonal invariant actionMeasurable
    weight (fun point => ‖field point‖ ^ 2) weightMeasurable
    ((Lp.stronglyMeasurable field).norm.measurable.pow_const 2) weightNonnegative
    (fun point => sq_nonneg _) weightIntegrable (Lp.memLp field).norm.integrable_sq

theorem realLp_norm_sq {Space Value : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (measure : Measure Space) (field : Lp Value 2 measure) :
    ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 ∂measure := by
  calc
    ‖field‖ ^ 2 = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ point, inner ℝ (field point) (field point) ∂measure := L2.inner_def field field
    _ = ∫ point, ‖field point‖ ^ 2 ∂measure := by simp only [real_inner_self_eq_norm_sq]

theorem physical_norm {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] : PhysicalNormGoal measure := by
  intro dimension domain domainMeasurable orthogonal invariant actionMeasurable
    weight weightMeasurable weightNonnegative weightIntegrable field
  have identity := (field_energy measure domain domainMeasurable orthogonal invariant
    actionMeasurable weight weightMeasurable weightNonnegative weightIntegrable field).2.2.2
  rw [← realLp_norm_sq (volume.restrict domain) field] at identity
  exact identity

end Grad.SchurKernel.RealEnergy
