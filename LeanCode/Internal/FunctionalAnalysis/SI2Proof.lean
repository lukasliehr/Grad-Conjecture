import SI2Tonelli
import DP1MeasurePreserving

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelPullback.Domain

namespace Grad.SchurKernel.Energy

variable {Parameter : Type*} [MeasurableSpace Parameter]

theorem product_energy (measure : Measure Parameter) [SigmaFinite measure] :
    ProductEnergyGoal measure := by
  intro domain domainMeasurable orthogonal invariant actionMeasurable
    weight energy weightMeasurable energyMeasurable
  exact product_energy_of_measurePreserving measure (volume.restrict domain)
    (fun parameter => orthogonal parameter) actionMeasurable
    (fun parameter => domainMeasurePreserving domain domainMeasurable
      (orthogonal parameter) (invariant parameter))
    weight energy weightMeasurable energyMeasurable

theorem swapped_energy (measure : Measure Parameter) [SigmaFinite measure] :
    SwappedEnergyGoal measure := by
  intro domain domainMeasurable orthogonal invariant actionMeasurable
    weight energy weightMeasurable energyMeasurable
  exact swapped_energy_of_measurePreserving measure (volume.restrict domain)
    (fun parameter => orthogonal parameter) actionMeasurable
    (fun parameter => domainMeasurePreserving domain domainMeasurable
      (orthogonal parameter) (invariant parameter))
    weight energy weightMeasurable energyMeasurable

theorem finite_energy (measure : Measure Parameter) [SigmaFinite measure] :
    FiniteEnergyGoal measure := by
  intro domain domainMeasurable orthogonal invariant actionMeasurable
    weight energy weightMeasurable energyMeasurable weightFinite energyFinite
  exact finite_energy_of_measurePreserving measure (volume.restrict domain)
    (fun parameter => orthogonal parameter) actionMeasurable
    (fun parameter => domainMeasurePreserving domain domainMeasurable
      (orthogonal parameter) (invariant parameter))
    weight energy weightMeasurable energyMeasurable weightFinite energyFinite

end Grad.SchurKernel.Energy
