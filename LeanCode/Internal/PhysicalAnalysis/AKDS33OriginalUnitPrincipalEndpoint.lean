import AKDS32OriginalUnitRowEstimates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The actual physical-length current has the full original rank and
adjustable pure-cell endpoint profile on the unit disk. -/
theorem current_endpoint (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) :
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => originalCurrentKernel (unitDiskAdmissible parameters) state.data.gaugeDeviation
        (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.current (unitDiskAdmissible parameters) rank state.data.gaugeDeviation
        (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative)).coarse) :=
  StartupUniformOriginalEndpoint.current (State:=OriginalUnitRankState parameters length radius)
    parameters (unitDiskAdmissible parameters) one_ne_zero one_ne_zero 12 rank
    (unitProfile (originalUnitFour parameters length radius))
    (unitProfile (complementExtensionConstant (originalUnitFour parameters length radius)))
    (fun _ => Nat.cast_nonneg _) (originalUnitFour_nonnegative parameters length radius)
    (fun _ => Nat.cast_nonneg _) (fun _ => abs_nonneg _)
    (fun state => state.field) (fun state => state.rho) (fun state => state.epsilon)
    (fun state => state.data.gaugeDeviation) (fun state => (state.coherent radiusNonnegative).2.2.2.1)
    (fun state => state.inverseCoherent radiusNonnegative)
    (fun state => (state.currentProfiles radiusNonnegative).1) (fun state => (state.currentProfiles radiusNonnegative).2)
    (fun state => state.unit)

/-- Both physical force rows and the signed flux retain their literal
original coefficients and share one high coefficient budget. -/
theorem rows_endpoint (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) :
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => startupGenuineForceKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.force (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).coarse) ∧
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => originalThirdCorrectionKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.third (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).coarse) ∧
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => originalFluxKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.flux (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).coarse) ∧
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => startupGenuinePrincipalFluxKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative))
      (fun state => (StartupRankOperator.principalFlux (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).coarse) := by
  exact StartupUniformOriginalEndpoint.actualRows (State:=OriginalUnitRankState parameters length radius)
    parameters (unitDiskAdmissible parameters) one_ne_zero one_ne_zero 12 rank
    (startupDeviationProfile (originalUnitFour parameters length radius)) (startupDeviationProfile (originalUnitFive parameters length))
    (fun _ => le_rfl) (originalUnitFour_nonnegative parameters length radius) (fun _ => le_rfl) (originalUnitFive_nonnegative parameters length)
    (fun state => state.field) (fun state => state.rho) (fun state => state.epsilon)
    (fun state => state.data) (fun state => state.coherent radiusNonnegative) (fun state => state.inverseCoherent radiusNonnegative)
    (fun state => (state.deviationProfiles radiusNonnegative).1)
    (fun state => (state.deviationProfiles radiusNonnegative).2.1)
    (fun state => (state.deviationProfiles radiusNonnegative).2.2) (fun state => state.unit)
    (current_endpoint parameters length radius radiusNonnegative rank)

/-- The SAME full original principal tensor has the existing adjustable
endpoint estimate for every physical length, including lengths below one. -/
theorem principal_endpoint (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) (outer inner : Fin 2) :
    StartupUniformOriginalEndpoint parameters (budget (parameters:=parameters) (length:=length) (radius:=radius) rank)
      (fun state => startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) outer inner)
      (fun state => (StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) outer inner).coarse) := by
  have rows := rows_endpoint parameters length radius radiusNonnegative rank
  exact StartupUniformOriginalEndpoint.actualPrincipal (State:=OriginalUnitRankState parameters length radius)
    (unitDiskAdmissible parameters) rank (budget rank) (budget_nonnegative rank)
    (fun state => state.data) (fun state => state.coherent radiusNonnegative) (fun state => state.inverseCoherent radiusNonnegative)
    rows.1 rows.2.1 rows.2.2.2 outer inner

end Grad.OriginalCoreRealization.OriginalUnitRankState
