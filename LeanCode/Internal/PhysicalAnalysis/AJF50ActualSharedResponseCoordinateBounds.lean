import AJF43SharedKnownHighCoordinateBound
import AJF45SharedKnownLowCoordinateBound
import AJF46FiniteSharedGeneratorTame
import AJD46SameCoupledInverseCoordinateBounds
import AJF36ActualApplicationTameConvolution
import AJF30AugmentedCoordinateBudget
import AJE54CompleteSourceOneHighBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCurrentSource Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.AnnularCrossOrbit

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule

attribute [local instance] sharedHighRealNormed sharedHighRealModule

variable (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L)
include lengthPositive

/-- Both complete known responses retain the same once-prescribed source. -/
theorem sharedKnownDiagonalOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => sharedKnownDiagonalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small) :=
  uniformCoordinateBound_pairReal
    (X := fun context : CoupledCoordinateContext parameters L compact => StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
    (E := fun context : CoupledCoordinateContext parameters L compact => CrossHighSpace context.lower L context.positive context.lengthPositive)
    (F := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    (sharedKnownHighResponseOrbit_uniformCoordinateBound parameters L compact)
    (sharedKnownLowResponseOrbit_uniformCoordinateBound parameters L compact lengthPositive)
    (fun context => sharedKnownHighResponseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => sharedKnownLowResponseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.state context.small)

/-- Actual full response calculus on the original ball. This discharges the
internal analytic premise of the finite/general-data graph transfer. -/
theorem sharedResponseCoordinateFamily_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (sharedResponseCoordinateFamily parameters L compact) := by
  have result := uniformCoordinateBound_complexRealComposition
    (X := fun context : CoupledCoordinateContext parameters L compact => StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
    (E := fun context : CoupledCoordinateContext parameters L compact => CoupledSpace context.lower L context.positive context.lengthPositive)
    (F := fun context : CoupledCoordinateContext parameters L compact => CoupledSpace context.lower L context.positive context.lengthPositive)
    (augmentedBudget CoupledCoordinateContext.budget)
    (fun context => coupledOrbitInverse parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf context.widthHalf context.widthLength context.state context.small)
    (fun context => sharedKnownDiagonalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small)
    (uniformCoordinateBound_augment CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact => coupledOrbitInverse parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf context.widthHalf context.widthLength context.state context.small)
      (coupledOrbitInverse_uniformCoordinateBound parameters L compact lengthPositive))
    (sharedKnownDiagonalOrbit_uniformCoordinateBound parameters L compact lengthPositive)
    (fun context => coupledOrbitInverse_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.widthHalf context.widthLength context.state context.small)
    (fun context => sharedKnownDiagonalOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small)
    (coupledAugmentedBudget_nonnegative parameters L compact)
    (fun order => 2 + pairBudgetConstant 8 order 1)
    (fun order => add_nonneg (by norm_num) (pairBudgetConstant_nonnegative 8 order (by norm_num)))
    (coupledAugmentedBudget_pair parameters L compact)
  intro axis order
  let constant := (result axis order).choose
  refine ⟨constant, (result axis order).choose_spec.1, ?_⟩
  intro context base time
  have estimate := (result axis order).choose_spec.2 context base time
  with_unfolding_all exact estimate

end Grad.AnnularHighGenerators
