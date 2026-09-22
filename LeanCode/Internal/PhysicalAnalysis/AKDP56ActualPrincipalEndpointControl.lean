import AKDP55ActualRowsEndpointControl

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1700000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupUniformOriginalEndpoint

/-- The literal complete principal tensor, with every reflected covector
and all three original rows, has the same original-core rank control. -/
theorem actualPrincipal {State : Type*} {parameters : PhaseParameters} {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (rank : ℕ)
    (budget : State → ℝ) (nonnegative : ∀ state,0≤budget state)
    (data : State → LedgerData L parameters.sigma0 parameters.gamma ell) (coherent : ∀ state,LedgerCoherent (data state))
    (inverseCoherent : ∀ state,FamilyCoherent (determinantInverseFamily admissible (data state).gaugeDeviation))
    (force : StartupUniformOriginalEndpoint parameters budget
      (fun state => startupGenuineForceKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.force admissible rank (data state) (coherent state) (inverseCoherent state)).coarse))
    (third : StartupUniformOriginalEndpoint parameters budget
      (fun state => originalThirdCorrectionKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.third admissible rank (data state) (coherent state) (inverseCoherent state)).coarse))
    (flux : StartupUniformOriginalEndpoint parameters budget
      (fun state => startupGenuinePrincipalFluxKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.principalFlux admissible rank (data state) (coherent state) (inverseCoherent state)).coarse))
    (outer inner : Fin 2) :
    StartupUniformOriginalEndpoint parameters budget
      (fun state => startupGenuinePrincipalTensorKernel admissible (data state) (coherent state) (inverseCoherent state) outer inner)
      (fun state => (StartupRankOperator.principalTensor admissible rank (data state) (coherent state) (inverseCoherent state) outer inner).coarse) := by
  have first := compFixed (StartupSpatialAction.value (L := L) (ell := ell) rank planarInclusionMap)
    (StartupSpatialAction.value_originalEndpointControlled parameters rank planarInclusionMap) force nonnegative
  have second := compFixed (StartupSpatialAction.value (L := L) (ell := ell) rank toroidalInclusionMap)
    (StartupSpatialAction.value_originalEndpointControlled parameters rank toroidalInclusionMap) third nonnegative
  have third := compFixed (StartupSpatialAction.value (L := L) (ell := ell) rank planarInclusionMap)
    (StartupSpatialAction.value_originalEndpointControlled parameters rank planarInclusionMap) flux nonnegative
  have first := compFixed (StartupSpatialAction.principalFixed (L := L) (ell := ell) rank outer inner 0)
    (StartupSpatialAction.principalFixed_originalEndpointControlled parameters rank outer inner 0) first nonnegative
  have second := compFixed (StartupSpatialAction.principalFixed (L := L) (ell := ell) rank outer inner 1)
    (StartupSpatialAction.principalFixed_originalEndpointControlled parameters rank outer inner 1) second nonnegative
  have third := compFixed (StartupSpatialAction.principalFixed (L := L) (ell := ell) rank outer inner 2)
    (StartupSpatialAction.principalFixed_originalEndpointControlled parameters rank outer inner 2) third nonnegative
  have combined := (first.add second).add third
  simp only [StartupSpatialAction.principalFixed_coarse,StartupSpatialAction.principalFixed_ranked] at combined
  unfold startupGenuinePrincipalTensorKernel
  simp only [Fin.sum_univ_three]
  exact combined

end StartupUniformOriginalEndpoint
end Grad.CartesianStartup
