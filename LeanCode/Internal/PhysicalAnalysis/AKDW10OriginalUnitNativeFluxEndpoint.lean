import AKDW9ExactNativeFluxSplit
import AKDS39OriginalUnitPrincipalAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.SourceCollarCoefficients Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger

/-- The actual scalar flux row inherits the full endpoint from the SAME
original signed flux, with the mean-free projection retained. -/
theorem scalarFlux_endpoint (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) :
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => originalScalarFluxKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.scalarFlux (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).coarse) := by
  have flux := (rows_endpoint parameters length radius radiusNonnegative rank).2.2.1
  have scalar := StartupUniformOriginalEndpoint.compFixed
    (StartupSpatialAction.value (L:=1) (ell:=1) rank toroidalPartMap)
    (StartupSpatialAction.value_originalEndpointControlled parameters rank toroidalPartMap) flux (budget_nonnegative rank)
  exact StartupUniformOriginalEndpoint.compFixed
    (StartupSpatialAction.scalarMeanFree (L:=1) (ell:=1) rank)
    (StartupSpatialAction.scalarMeanFree_originalEndpointControlled parameters rank) scalar (budget_nonnegative rank)

/-- Actual physical-L pre-axial coefficient flux, before its single
physical axial derivative, has the common one-high endpoint. -/
theorem nativePreAxial_endpoint (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) (direction : Fin 2) :
    ∃ ranked : OriginalUnitRankState parameters length radius → StartupL2 (startupTensorDimension 3 rank) →L[ℂ] StartupL2 (startupTensorDimension 3 rank),
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)) direction) ranked :=
  startupNativePreAxialFlux_endpoint parameters rank (budget rank) (budget_nonnegative rank) _ _ _ _
    (rows_endpoint parameters length radius radiusNonnegative rank).1
    (scalarFlux_endpoint parameters length radius radiusNonnegative rank) direction

/-- The actual principal image exists in the unchanged original core. -/
theorem principal_core_exists {parameters : PhaseParameters} {length radius : ℝ}
    (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius)
    (core : ACore parameters 3) (outer inner : Fin 2) :
    ∃ image : ACore parameters 3, originalSourceFieldLinear parameters image=
      startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) outer inner
        (originalSourceFieldLinear parameters core) := by
  have endpoint := principal_endpoint parameters length radius radiusNonnegative 0 outer inner
  let actual := (endpoint.1.choose_spec state).some
  exact ⟨actual.action core,actual.same core⟩

/-- The same coefficient part of the actual lower flux is an original core. -/
theorem nativePreAxial_core_exists {parameters : PhaseParameters} {length radius : ℝ}
    (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius)
    (core : ACore parameters 3) (direction : Fin 2) :
    ∃ image : ACore parameters 3, originalSourceFieldLinear parameters image=
      startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)) direction
        (originalSourceFieldLinear parameters core) := by
  let certificate := nativePreAxial_endpoint parameters length radius radiusNonnegative 0 direction
  let endpoint := certificate.choose_spec
  let actual := (endpoint.1.choose_spec state).some
  exact ⟨actual.action core,actual.same core⟩

end Grad.OriginalCoreRealization.OriginalUnitRankState
