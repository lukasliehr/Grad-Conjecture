import AJF42FullKnownPhysicalCoordinateBound
import AJF27SameSharedKnownHighResponse
import AJE22SharedKnownFunctionalTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus Grad.ClosedJets Grad.SourceCollarDivision
open Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularStrongOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentGreen

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

open Grad.AnnularCoupledInverse
attribute [local instance] sharedHighRealNormed sharedHighRealModule

theorem sharedKnownInput_norm (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    ‖sharedKnownInput parameters lower positive lowerHalf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro data
  exact (sharedHighKnownInput_bound parameters lower positive lowerHalf data).trans_eq (one_mul _).symm

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem sharedKnownEnergyOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => sharedKnownEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) :=
  uniformCoordinateBound_precomposeReal (knownHighEnergyOrbit_uniformCoordinateBound parameters L compact)
    (fun context => knownHighEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => sharedKnownInput parameters context.lower context.positive context.lowerHalf) 1 (by norm_num)
    (fun context => sharedKnownInput_norm parameters context.lower context.positive context.lowerHalf)

theorem sharedKnownPhysicalOutputOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => sharedKnownPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) :=
  uniformCoordinateBound_precomposeReal (knownPhysicalOutputOrbit_uniformCoordinateBound parameters L compact)
    (fun context => knownPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => sharedKnownInput parameters context.lower context.positive context.lowerHalf) 1 (by norm_num)
    (fun context => sharedKnownInput_norm parameters context.lower context.positive context.lowerHalf)

/-- The fixed literal physical coordinate map followed by the original
closed graph projection; the actual field equality is already proved in26. -/
def knownFluxDecoder (context : CoupledCoordinateContext parameters L compact) :
    DivisionRow 3 context.lower →L[ℝ] annularOmegaGraph context.lower L context.positive context.lengthPositive :=
  ((annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto.restrictScalars ℝ).comp
    ((physicalOmegaCoordinates parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).restrictScalars ℝ)

theorem knownFluxDecoder_norm (context : CoupledCoordinateContext parameters L compact) :
    ‖knownFluxDecoder parameters L compact context‖ ≤ 4 := by
  have projection : ‖(annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto.restrictScalars ℝ‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.norm_restrictScalars] using
      (annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto_norm_le
  have coordinates : ‖(physicalOmegaCoordinates parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).restrictScalars ℝ‖ ≤ 4 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    exact physicalOmegaCoordinates_bound parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul projection coordinates (norm_nonneg _) zero_le_one).trans_eq (one_mul 4))

theorem sharedKnownFluxOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => sharedKnownFluxOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have estimate := uniformCoordinateBound_postcomposeReal (sharedKnownPhysicalOutputOrbit_uniformCoordinateBound parameters L compact)
    (fun context => sharedKnownPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (knownFluxDecoder parameters L compact) 4 (by norm_num) (knownFluxDecoder_norm parameters L compact)
  exact estimate

theorem sharedKnownHighResponseOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact => sharedKnownHighResponseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small)) :=
  uniformCoordinateBound_pairReal (sharedKnownEnergyOrbit_uniformCoordinateBound parameters L compact)
    (sharedKnownFluxOrbit_uniformCoordinateBound parameters L compact)
    (fun context => sharedKnownEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => sharedKnownFluxOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))

end Grad.AnnularHighGenerators
