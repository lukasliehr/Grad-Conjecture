import AJF30AugmentedCoordinateBudget
import AJE21FullKnownFunctionalBaseBound
import AJF23SameKnownHighEnergyOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularStrongOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularOrbitGenerators

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The original complete prescribed forcing functional, with the constant
coefficient part retained explicitly in its positive-order budget. -/
theorem knownFunctionalOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        knownFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state 0 0) := by
  apply uniformCoordinateBound_of_realJet (augmentedBudget CoupledCoordinateContext.budget)
    (fun context angular cell => knownFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state angular cell)
    (fun context => knownFunctionalOrbitJet_hasFDerivAt parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state)
  intro angular cell
  by_cases zero : angular + cell = 0
  · have angularZero : angular = 0 := by omega
    have cellZero : cell = 0 := by omega
    subst angular
    subst cell
    obtain ⟨constant, nonnegative, estimate⟩ := knownFunctionalOrbitJet_base_bound parameters L compact
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    simpa only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one] using
      estimate context.state context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf
        context.widthLength context.budget_zero_le_one tau
  · obtain ⟨constant, nonnegative, estimate⟩ := knownFunctionalOrbitJet_positive_oneHigh parameters L compact angular cell (by omega)
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    rw [coordinateJetWeight, if_neg zero]
    have bound := estimate context.state context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength tau
    change _ ≤ constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
      context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (1 + (angular + cell) + 7)) at bound
    change _ ≤ constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
      context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (8 + (angular + cell)))
    simpa only [show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using bound

/-- Actual complete bulk output includes direct forcing at order zero and
its original kernel derivative at every positive order. -/
theorem knownBulkOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        knownBulkOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.state 0 0) := by
  apply uniformCoordinateBound_of_realJet (augmentedBudget CoupledCoordinateContext.budget)
    (fun context angular cell => knownBulkOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.state angular cell)
    (fun context => knownBulkOrbitJet_hasFDerivAt parameters L compact context.lower context.positive context.lowerHalf context.state)
  intro angular cell
  by_cases zero : angular + cell = 0
  · have angularZero : angular = 0 := by omega
    have cellZero : cell = 0 := by omega
    subst angular
    subst cell
    obtain ⟨constant, nonnegative, estimate⟩ := knownBulkOrbitJet_base_bound parameters L compact
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    simpa only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one] using
      estimate context.state context.lower context.positive context.lowerHalf context.budget_zero_le_one tau
  · obtain ⟨constant, nonnegative, estimate⟩ := knownBulkOrbitJet_positive_oneHigh parameters L compact angular cell (by omega)
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    rw [coordinateJetWeight, if_neg zero]
    have bound := estimate context.state context.lower context.positive context.lowerHalf tau
    change _ ≤ constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
      context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (1 + (angular + cell) + 7)) at bound
    change _ ≤ constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
      context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (8 + (angular + cell)))
    simpa only [show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using bound

end Grad.AnnularHighGenerators
