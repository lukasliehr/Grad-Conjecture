import AKDP79NativeLowerFluxFixedActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

def startupNativePreAxialFluxKernel (force : StartupL2 3 →L[ℂ] StartupL2 2)
    (scalarFlux : StartupL2 3 →L[ℂ] StartupL2 1) (direction : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  (startupLowerScalarFluxKernel direction).comp (scalarFlux-originalValueKernel toroidalPartMap)-
    (originalValueKernel (startupComponentEntry (2 : Fin 3) direction)).comp
      (startupGradientVectorKernel-startupCovariantPrimitiveKernel.comp force)

/-- The actual native lower-flux coefficient formula, before its single
explicit axial derivative, retains the complete one-high endpoint. -/
theorem startupNativePreAxialFlux_endpoint {State : Type*} (parameters : PhaseParameters) (rank : ℕ)
    (budget : State → ℝ) (nonnegative : ∀ state,0≤budget state)
    (force : State → StartupL2 3 →L[ℂ] StartupL2 2) (scalarFlux : State → StartupL2 3 →L[ℂ] StartupL2 1)
    (forceRank : State → StartupL2 (startupTensorDimension 3 rank) →L[ℂ] StartupL2 (startupTensorDimension 2 rank))
    (scalarRank : State → StartupL2 (startupTensorDimension 3 rank) →L[ℂ] StartupL2 (startupTensorDimension 1 rank))
    (forceEstimate : StartupUniformOriginalEndpoint parameters budget force forceRank)
    (scalarEstimate : StartupUniformOriginalEndpoint parameters budget scalarFlux scalarRank) (direction : Fin 2) :
    ∃ ranked : State → StartupL2 (startupTensorDimension 3 rank) →L[ℂ] StartupL2 (startupTensorDimension 3 rank),
      StartupUniformOriginalEndpoint parameters budget (fun state => startupNativePreAxialFluxKernel (force state) (scalarFlux state) direction) ranked := by
  have scalar := scalarEstimate.sub
    ((StartupSpatialAction.value_originalEndpointControlled (L := 1) (ell := 1) parameters rank toroidalPartMap).onBudget budget nonnegative)
  have lower := StartupUniformOriginalEndpoint.compFixed
    (StartupSpatialAction.lowerScalarFlux (L := 1) (ell := 1) rank direction)
    (StartupSpatialAction.lowerScalarFlux_originalEndpointControlled parameters rank direction) scalar nonnegative
  have forcePrimitive := StartupUniformOriginalEndpoint.compFixed
    (StartupSpatialAction.covariantPrimitive (L := 1) (ell := 1) rank)
    (StartupSpatialAction.covariantPrimitive_originalEndpointControlled parameters rank) forceEstimate nonnegative
  have gradient := ((StartupSpatialAction.gradientVectorPart_originalEndpointControlled (L := 1) (ell := 1)
    parameters rank).onBudget budget nonnegative).sub forcePrimitive
  have entry := StartupUniformOriginalEndpoint.compFixed
    (StartupSpatialAction.value (L := 1) (ell := 1) rank (startupComponentEntry (2 : Fin 3) direction))
    (StartupSpatialAction.value_originalEndpointControlled parameters rank (startupComponentEntry (2 : Fin 3) direction)) gradient nonnegative
  refine ⟨fun state =>
    (StartupSpatialAction.lowerScalarFlux (L := 1) (ell := 1) rank direction).ranked.coarse.comp
      (scalarRank state-(StartupSpatialAction.value (L := 1) (ell := 1) rank toroidalPartMap).ranked.coarse)-
    (StartupSpatialAction.value (L := 1) (ell := 1) rank (startupComponentEntry (2 : Fin 3) direction)).ranked.coarse.comp
      ((StartupSpatialAction.gradientVectorPart (L := 1) (ell := 1) rank).ranked.coarse-
        (StartupSpatialAction.covariantPrimitive (L := 1) (ell := 1) rank).ranked.coarse.comp (forceRank state)),?_⟩
  have scalarPoint : (StartupSpatialAction.value (L := 1) (ell := 1) rank toroidalPartMap).signed.coarse = originalValueKernel toroidalPartMap := rfl
  have gradientPoint : (StartupSpatialAction.value (L := 1) (ell := 1) rank (startupComponentEntry (2 : Fin 3) direction)).signed.coarse =
      originalValueKernel (startupComponentEntry (2 : Fin 3) direction) := rfl
  simpa only [scalarPoint,gradientPoint,startupLowerScalarFluxKernel_coarse,StartupSpatialAction.covariantPrimitive_coarse,
    startupGradientVectorKernel_coarse,startupNativePreAxialFluxKernel] using lower.sub entry

/-- Exact pre-axial coefficient part of the same native flux. The known
force is kept separate for independent source payment. -/
theorem startupNativePreAxialFluxKernel_value (force : StartupL2 3 →L[ℂ] StartupL2 2)
    (scalarFlux : StartupL2 3 →L[ℂ] StartupL2 1) (field : StartupL2 3) (direction : Fin 2) :
    startupNativePreAxialFluxKernel force scalarFlux direction field=
      startupERLowerFlux (scalarFlux field-originalValueKernel toroidalPartMap field)
        (startupRecoveredGradient (originalValueKernel planarPartMap field) (-force field)) direction := by
  rw [startupERLowerFlux_linear]
  change startupLowerScalarFluxKernel direction (scalarFlux field-originalValueKernel toroidalPartMap field)-
    originalValueKernel (startupComponentEntry (2 : Fin 3) direction)
      (startupGradientVectorKernel field-startupCovariantPrimitiveKernel (force field)) = _
  congr 1
  congr 1
  unfold startupGradientVectorKernel startupRecoveredGradient originalPlanarMeanFreeKernel
  simp only [add_apply,sub_apply,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_add,map_neg,map_smul]
  abel

end Grad.CartesianStartup
