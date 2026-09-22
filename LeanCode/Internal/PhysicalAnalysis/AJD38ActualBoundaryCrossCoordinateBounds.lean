import AJD36UniformClosedGraphAndPair
import AJD37ActualBoundaryDeviationCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularCrossMaps

local instance lowBoundaryAmbientOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (lowEnergyGraph lower L positive →L[ℂ] NegativeTrace parameters 0 0 1) := inferInstance
local instance lowBoundaryAmbientOperatorRealNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (lowEnergyGraph lower L positive →L[ℂ] NegativeTrace parameters 0 0 1) := ContinuousLinearMap.toNormedSpace

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem lowToHighBoundaryAmbientOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        lowToHighBoundaryAmbientOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state) := by
  have inputBound (context : CoupledCoordinateContext parameters L compact) :
      ‖(sevenSlotFlatten parameters 0 0).comp (lowOuterSevenTrace parameters context.lower L context.lengthPositive context.positive context.lowerHalf)‖ ≤
        |lowOuterSevenConstant L| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
    intro field
    rw [ContinuousLinearMap.comp_apply, sevenSlotFlatten_norm]
    exact (lowOuterSevenLinear_bound parameters context.lower L context.lengthPositive context.positive context.lowerHalf field).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg field))
  have mapped := (actualBoundaryDeviation_uniformCoordinateBound parameters L compact).precomposeComplex
    (fun context => boundaryOrbitJetAction_contDiff parameters 0 0 context.state.boundaryState.fullBoundaryDeviation 0 0)
    (fun context => (sevenSlotFlatten parameters 0 0).comp (lowOuterSevenTrace parameters context.lower L context.lengthPositive context.positive context.lowerHalf))
    |lowOuterSevenConstant L| (abs_nonneg _) inputBound
  exact mapped.neg (fun context => complexOperatorComposition_contDiff _ _
    (boundaryOrbitJetAction_contDiff parameters 0 0 context.state.boundaryState.fullBoundaryDeviation 0 0) contDiff_const)

/-- The actual negative physical boundary cross response is estimated in
its original high primitive carrier, with no assumed translated membership. -/
theorem lowToHighBoundaryOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        lowToHighBoundaryOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state) := by
  have mapped := (lowToHighBoundaryAmbientOrbit_uniformCoordinateBound parameters L compact).postcomposeComplex
    (F := fun _ => HighBoundaryPrimitive parameters 0 0)
    (fun context => lowToHighBoundaryAmbientOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (fun _ => (highAngularSubmodule parameters 0 0 1).orthogonalProjectionOnto)
    1 (by norm_num)
    (fun _ => (highAngularSubmodule parameters 0 0 1).orthogonalProjectionOnto_norm_le)
  have same (context : CoupledCoordinateContext parameters L compact) (tau : OrbitParameter) :
      (highAngularSubmodule parameters 0 0 1).orthogonalProjectionOnto.comp
        (lowToHighBoundaryAmbientOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state tau) =
      lowToHighBoundaryOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state tau := by
    exact (congrArg (graphOperatorProjection (X := lowEnergyGraph context.lower L context.positive) (highAngularSubmodule parameters 0 0 1))
      (lowToHighBoundaryOrbit_inclusion parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state tau).symm).trans
      (graphOperatorProjection_retract _ _)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := mapped axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [same] at converted
  with_unfolding_all exact converted
end Grad.AnnularCrossOrbit
