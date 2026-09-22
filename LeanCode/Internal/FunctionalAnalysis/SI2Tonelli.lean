import SI2Interface

noncomputable section

open MeasureTheory

namespace Grad.SchurKernel.Energy

variable {Parameter Space : Type*} [MeasurableSpace Parameter] [MeasurableSpace Space]

theorem product_energy_of_measurePreserving
    (parameterMeasure : Measure Parameter) (spatialMeasure : Measure Space)
    [SFinite parameterMeasure] [SFinite spatialMeasure]
    (action : Parameter → Space → Space)
    (actionMeasurable : Measurable (fun pair : Parameter × Space => action pair.1 pair.2))
    (preserving : ∀ parameter, MeasurePreserving (action parameter) spatialMeasure spatialMeasure)
    (weight : Parameter → ENNReal) (energy : Space → ENNReal)
    (weightMeasurable : Measurable weight) (energyMeasurable : Measurable energy) :
    (∫⁻ pair : Parameter × Space, weight pair.1 * energy (action pair.1 pair.2)
      ∂parameterMeasure.prod spatialMeasure) =
      (∫⁻ parameter, weight parameter ∂parameterMeasure) *
        ∫⁻ point, energy point ∂spatialMeasure := by
  have integrandMeasurable : Measurable (fun pair : Parameter × Space =>
      weight pair.1 * energy (action pair.1 pair.2)) :=
    (weightMeasurable.comp measurable_fst).mul (energyMeasurable.comp actionMeasurable)
  have sectionLaw (parameter : Parameter) :
      (∫⁻ point, weight parameter * energy (action parameter point) ∂spatialMeasure) =
        weight parameter * ∫⁻ point, energy point ∂spatialMeasure := by
    have sectionMeasurable : Measurable (fun point => energy (action parameter point)) :=
      energyMeasurable.comp (preserving parameter).measurable
    calc
      _ = weight parameter * ∫⁻ point, energy (action parameter point) ∂spatialMeasure :=
        lintegral_const_mul (weight parameter) sectionMeasurable
      _ = _ := congrArg (fun integral => weight parameter * integral)
        ((preserving parameter).lintegral_comp energyMeasurable)
  rw [lintegral_prod _ integrandMeasurable.aemeasurable]
  simp_rw [sectionLaw]
  exact lintegral_mul_const _ weightMeasurable

theorem swapped_energy_of_measurePreserving
    (parameterMeasure : Measure Parameter) (spatialMeasure : Measure Space)
    [SFinite parameterMeasure] [SFinite spatialMeasure]
    (action : Parameter → Space → Space)
    (actionMeasurable : Measurable (fun pair : Parameter × Space => action pair.1 pair.2))
    (preserving : ∀ parameter, MeasurePreserving (action parameter) spatialMeasure spatialMeasure)
    (weight : Parameter → ENNReal) (energy : Space → ENNReal)
    (weightMeasurable : Measurable weight) (energyMeasurable : Measurable energy) :
    (∫⁻ point, ∫⁻ parameter, weight parameter * energy (action parameter point)
      ∂parameterMeasure ∂spatialMeasure) =
      (∫⁻ parameter, weight parameter ∂parameterMeasure) *
        ∫⁻ point, energy point ∂spatialMeasure := by
  have integrandMeasurable : Measurable (fun pair : Parameter × Space =>
      weight pair.1 * energy (action pair.1 pair.2)) :=
    (weightMeasurable.comp measurable_fst).mul (energyMeasurable.comp actionMeasurable)
  exact (lintegral_prod_symm _ integrandMeasurable.aemeasurable).symm.trans
    (product_energy_of_measurePreserving parameterMeasure spatialMeasure action
      actionMeasurable preserving weight energy weightMeasurable energyMeasurable)

theorem finite_energy_of_measurePreserving
    (parameterMeasure : Measure Parameter) (spatialMeasure : Measure Space)
    [SFinite parameterMeasure] [SFinite spatialMeasure]
    (action : Parameter → Space → Space)
    (actionMeasurable : Measurable (fun pair : Parameter × Space => action pair.1 pair.2))
    (preserving : ∀ parameter, MeasurePreserving (action parameter) spatialMeasure spatialMeasure)
    (weight : Parameter → ENNReal) (energy : Space → ENNReal)
    (weightMeasurable : Measurable weight) (energyMeasurable : Measurable energy)
    (weightFinite : (∫⁻ parameter, weight parameter ∂parameterMeasure) < ⊤)
    (energyFinite : (∫⁻ point, energy point ∂spatialMeasure) < ⊤) :
    (∫⁻ point, ∫⁻ parameter, weight parameter * energy (action parameter point)
      ∂parameterMeasure ∂spatialMeasure) < ⊤ ∧
      ∀ᵐ point ∂spatialMeasure,
        (∫⁻ parameter, weight parameter * energy (action parameter point) ∂parameterMeasure) < ⊤ := by
  have integralFinite : (∫⁻ point, ∫⁻ parameter,
      weight parameter * energy (action parameter point) ∂parameterMeasure ∂spatialMeasure) < ⊤ := by
    rw [swapped_energy_of_measurePreserving parameterMeasure spatialMeasure action
      actionMeasurable preserving weight energy weightMeasurable energyMeasurable]
    exact ENNReal.mul_lt_top weightFinite energyFinite
  refine ⟨integralFinite, ?_⟩
  apply ae_lt_top _ integralFinite.ne
  exact ((weightMeasurable.comp measurable_fst).mul
    (energyMeasurable.comp actionMeasurable)).lintegral_prod_left'

end Grad.SchurKernel.Energy
