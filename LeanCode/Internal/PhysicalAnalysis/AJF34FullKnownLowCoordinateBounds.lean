import AJF33UniformRealOperatorOperations
import AJE34KnownLowBaseAndSharedBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularStrongOrbit
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularStrongData Grad.AnnularKnownLow
open Grad.AnnularReconstruction Grad.AnnularOrbitGenerators

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The complete AIR source map has the genuine uniform coordinate tower,
including direct forcing and the independent actual incoming datum. -/
theorem knownLowDataOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        knownLowDataOrbitJet parameters L compact context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) context.state 0 0) := by
  apply uniformCoordinateBound_of_realJet (augmentedBudget CoupledCoordinateContext.budget)
    (fun context angular cell => knownLowDataOrbitJet parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state angular cell)
    (fun context => knownLowDataOrbitJet_hasFDerivAt parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state)
  intro angular cell
  by_cases zero : angular + cell = 0
  · have angularZero : angular = 0 := by omega
    have cellZero : cell = 0 := by omega
    subst angular
    subst cell
    refine ⟨knownLowBaseConstant parameters L compact, knownLowBaseConstant_nonnegative parameters L compact, ?_⟩
    intro context tau
    simpa only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one] using
      knownLowDataOrbitJet_base_bound parameters L compact context.lower context.positive
        (context.lowerHalf.trans (by norm_num)) context.state context.budget_zero_le_one tau
  · obtain ⟨constant, nonnegative, estimate⟩ := knownLowDataOrbitJet_oneHigh parameters L compact angular cell (by omega)
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    rw [coordinateJetWeight, if_neg zero]
    have bound := estimate context.state context.lower context.positive (context.lowerHalf.trans (by norm_num)) tau
    apply bound.trans
    apply mul_le_mul_of_nonneg_left _ nonnegative
    change _ ≤ 1 + _
    exact (Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_monotone _ _ _ _ (by omega)).trans
      (le_add_of_nonneg_left zero_le_one)

theorem sharedLowDataOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        sharedLowDataOrbitJet parameters L compact context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) context.state 0 0) := by
  apply uniformCoordinateBound_precomposeReal (knownLowDataOrbit_uniformCoordinateBound parameters L compact)
    (fun context => knownLowDataOrbitJet_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state 0 0)
    (fun context => strongToLow parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
    1 (by norm_num)
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro data
  simpa only [one_mul] using strongToLow_bound parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 data

end Grad.AnnularHighGenerators
