import ConfigurationRegularityConsumer
import ModuliTopologyConsumer
import ModuliCurveNonisolationConsumer

noncomputable section

namespace Grad.MainAssembly.ModuliCurveAssembly

open Grad.MainTarget
open Grad.MainAssembly.ConfigurationRegularity
open Grad.MainAssembly.TargetModuliTopology.Consumer
open Grad.MainAssembly.TargetRelation
open Grad.MainAssembly.ModuliCurveNonisolation.Consumer

/-- The canonical validity witness supplied by the physical conclusions. This
named proof term keeps the dependent configuration curves definitionally
identical in all downstream hypotheses. -/
theorem physicalValidity
    {interval : Set ℝ} (regularity : Regularity)
    (family : interval → Representative) (cellLength : ℝ) (period : ℕ)
    (conclusions : ∀ parameter,
      PhysicalConclusions (family parameter) cellLength period) :
    ∀ parameter, IsConfiguration regularity (family parameter) :=
  fun parameter => isConfiguration_of_physicalConclusions regularity
    (family parameter) cellLength period (conclusions parameter)

/-- Injectivity of a curve in the exact generated target quotient is
equivalent to cancellation of one literal full `Related` witness. -/
theorem moduliClassCurve_injective_iff_related_cancellation
    {interval : Set ℝ} (regularity : Regularity)
    (family : interval → Representative)
    (validity : ∀ parameter, IsConfiguration regularity (family parameter)) :
    Function.Injective (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity)) ↔
      ∀ first second : interval,
        Related regularity
          (⟨family first, validity first⟩ : Configuration regularity)
          (⟨family second, validity second⟩ : Configuration regularity) →
        first = second := by
  constructor
  · intro curveInjective first second related
    apply curveInjective
    exact (moduliClass_eq_iff_related regularity
      (⟨family first, validity first⟩ : Configuration regularity)
      (⟨family second, validity second⟩ : Configuration regularity)).mpr related
  · intro relatedCancellation first second classEquality
    apply relatedCancellation first second
    exact (moduliClass_eq_iff_related regularity
      (⟨family first, validity first⟩ : Configuration regularity)
      (⟨family second, validity second⟩ : Configuration regularity)).mp classEquality

/-- Exact target assembly: physical conclusions discharge configuration
validity, target configuration continuity descends through the quotient, a
literal `Related` cancellation theorem gives injectivity, and `NG_CAL112`
supplies singleton non-openness. -/
theorem moduliCurve_of_physicalConclusions
    {interval : Set ℝ} (regularity : Regularity)
    (family : interval → Representative) (cellLength : ℝ) (period : ℕ)
    (conclusions : ∀ parameter,
      PhysicalConclusions (family parameter) cellLength period)
    (configurationContinuous : Continuous (fun parameter =>
      (⟨family parameter,
        physicalValidity regularity family cellLength period conclusions parameter⟩ :
          Configuration regularity)))
    (relatedCancellation : ∀ first second : interval,
      Related regularity
        (⟨family first,
          physicalValidity regularity family cellLength period conclusions first⟩ :
            Configuration regularity)
        (⟨family second,
          physicalValidity regularity family cellLength period conclusions second⟩ :
            Configuration regularity) →
      first = second) :
    ModuliCurve regularity interval family := by
  let validity := physicalValidity regularity family cellLength period conclusions
  have quotientContinuous : Continuous (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity)) := by
    apply continuous_moduli_curve regularity family validity
    exact configurationContinuous
  have quotientInjective : Function.Injective (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity)) :=
    (moduliClassCurve_injective_iff_related_cancellation
      regularity family validity).mpr relatedCancellation
  exact moduliCurve_of_continuous_injective regularity family validity
    quotientContinuous quotientInjective

end Grad.MainAssembly.ModuliCurveAssembly
