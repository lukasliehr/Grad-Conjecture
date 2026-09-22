import AJF39FullKnownEnergyCoordinateBound
import AJD28ActualCoefficientCoordinateBounds
import AJF25SameKnownPhysicalOutputOrbit

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

theorem energyPhysicalOutputOrbit_uniformCoordinateBound (parameters : PhaseParameters) (L compact : ℝ) :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => energyPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state) := by
  have coefficient := uniformCoordinateBound_augment CoupledCoordinateContext.budget
    (fun context : CoupledCoordinateContext parameters L compact => actualEliminatedOrbit parameters L compact context.lower
      context.positive (context.lowerHalf.trans (by norm_num)) context.state 0)
    (actualEliminatedOrbit_uniformCoordinateBound parameters L compact)
  apply coefficient.map_bound
    (fun context => actualEliminatedOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state)
    (fun context => realInputPrecompose ((highEightEnergyPacket parameters context.lower L context.positive
      context.lengthPositive context.widthHalf context.widthLength).restrictScalars ℝ)) (4 + 2 * |L|) (by positivity)
  intro context operator
  apply (realInputPrecompose_bound _ operator).trans
  apply (mul_le_mul_of_nonneg_left _ (norm_nonneg operator)).trans_eq (mul_comm _ _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact highEightEnergyPacket_bound parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength

/-- The literal full known physical output has the same one-high coordinate
bound as its genuine elimination kernels and actual full energy solution. -/
theorem knownPhysicalOutputOrbit_uniformCoordinateBound (parameters : PhaseParameters) (L compact : ℝ) :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => knownPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have solution := (energyPhysicalOutputOrbit_uniformCoordinateBound parameters L compact).composeReal
    (knownHighEnergyOrbit_uniformCoordinateBound parameters L compact)
    (fun context => energyPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state)
    (fun context => knownHighEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (coupledAugmentedBudget_nonnegative parameters L compact)
    (fun order => 2 + Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant 8 order 1)
    (fun order => add_nonneg (by norm_num) (Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant_nonnegative 8 order (by norm_num)))
    (coupledAugmentedBudget_pair parameters L compact)
  exact solution.add (knownBulkOrbit_uniformCoordinateBound parameters L compact)
    (fun context => realOperatorComposition_contDiff _ _
      (energyPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state)
      (knownHighEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)))
    (fun context => knownBulkOrbitJet_contDiff parameters L compact context.lower context.positive context.lowerHalf context.state 0 0)

end Grad.AnnularHighGenerators
