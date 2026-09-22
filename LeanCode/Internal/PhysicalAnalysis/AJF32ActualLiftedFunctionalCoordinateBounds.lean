import AJF30AugmentedCoordinateBudget
import AJF20ActualSolverAxisBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularReconstruction Grad.AnnularOrbitGenerators
open Grad.AnnularCoupledInverse

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem liftedFunctionalPositive_bound (context : CoupledCoordinateContext parameters L compact)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) (tau : OrbitParameter) :
    ‖liftedTestFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state angular cell tau‖ ≤
      actualHighJetConstant parameters L compact angular cell * context.budget (angular + cell) := by
  have full := (currentHighFormOrbitJet_oneHigh parameters L compact angular cell orderPositive).choose_spec.2
    context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state tau
  have bound := (liftedTestFunctionalOrbitJet_norm parameters L compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.widthHalf context.widthLength context.state angular cell tau).trans full
  simpa only [actualHighJetConstant, dif_pos orderPositive, CoupledCoordinateContext.budget,
    AnnularReconstructionState.errorBudget, show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using bound

/-- The actual full field/test form, restricted only in its test variable,
has genuine uniformly bounded pure-axis derivatives on the same B8 ball. -/
theorem liftedTestFunctionalOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        liftedTestFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state 0 0) := by
  apply uniformCoordinateBound_of_realJet CoupledCoordinateContext.budget
    (fun context angular cell => liftedTestFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state angular cell)
    (fun context => liftedTestFunctionalOrbitJet_hasFDerivAt parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state)
  intro angular cell
  by_cases zero : angular + cell = 0
  · have angularZero : angular = 0 := by omega
    have cellZero : cell = 0 := by omega
    subst angular
    subst cell
    refine ⟨5, by norm_num, ?_⟩
    intro context tau
    simpa only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one] using
      liftedTestFunctionalOrbit_zero_norm parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state
        (coupledPrimitive_highSmall parameters L compact context.state context.small) tau
  · refine ⟨actualHighJetConstant parameters L compact angular cell,
      actualHighJetConstant_nonnegative parameters L compact angular cell, ?_⟩
    intro context tau
    exact (liftedFunctionalPositive_bound parameters L compact context angular cell (by omega) tau).trans_eq
      (congrArg (fun weight : ℝ => actualHighJetConstant parameters L compact angular cell * weight)
        (show context.budget (angular + cell) = coordinateJetWeight context.budget (angular + cell) from by
          simp only [coordinateJetWeight, if_neg zero]))

end Grad.AnnularHighGenerators
