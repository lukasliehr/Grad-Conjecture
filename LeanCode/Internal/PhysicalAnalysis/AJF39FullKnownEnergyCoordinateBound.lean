import AJF37ActualIncomingCoordinateBound
import AJF38KnownZeroFunctionalCoordinateBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularStrongOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularOrbitGenerators Grad.AnnularCoupledInverse
open Grad.AnnularHighInverseOrbit Grad.AnnularCurrentSource

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

theorem knownIncomingProjection_norm (parameters : PhaseParameters) (lower : ℝ) :
    ‖highKnownIncomingProjection parameters lower 0 0‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro data
  change ‖data.ofLp.2.ofLp.2.ofLp.2‖ ≤ 1 * ‖data‖
  simpa only [one_mul] using (hilbert_second_bound data.ofLp.2.ofLp.2).trans
    ((hilbert_second_bound data.ofLp.2).trans (hilbert_second_bound data))

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The full actual known high energy response has one augmented high
factor, uniformly before the original lower radius and retained state. -/
theorem knownHighEnergyOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        knownHighEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have inverse := uniformCoordinateBound_augment CoupledCoordinateContext.budget
    (fun context : CoupledCoordinateContext parameters L compact => highSourceSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (highSourceSolverOrbit_uniformCoordinateBound parameters L compact)
  have source := inverse.composeReal (knownZeroFunctionalOrbit_uniformCoordinateBound parameters L compact)
    (fun context => highSourceSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) (fun context => knownZeroFunctionalOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state)
    (coupledAugmentedBudget_nonnegative parameters L compact)
    (fun order => 2 + Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant 8 order 1)
    (fun order => add_nonneg (by norm_num) (Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant_nonnegative 8 order (by norm_num)))
    (coupledAugmentedBudget_pair parameters L compact)
  have incomingBase := uniformCoordinateBound_augment CoupledCoordinateContext.budget
    (fun context : CoupledCoordinateContext parameters L compact => highIncomingSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (highIncomingSolverOrbit_uniformCoordinateBound parameters L compact)
  have incoming := uniformCoordinateBound_precomposeReal incomingBase
    (fun context => highIncomingSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => highKnownIncomingProjection parameters context.lower 0 0) 1 (by norm_num)
    (fun context => knownIncomingProjection_norm parameters context.lower)
  exact source.add incoming
    (fun context => realOperatorComposition_contDiff _ _ (highSourceSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) (knownZeroFunctionalOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state))
    (fun context => realOperatorComposition_contDiff _ _ (highIncomingSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) contDiff_const)

end Grad.AnnularHighGenerators
