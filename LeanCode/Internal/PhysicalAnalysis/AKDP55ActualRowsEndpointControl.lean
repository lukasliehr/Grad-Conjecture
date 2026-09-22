import AKDP54ActualCurrentEndpointControl

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1800000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupUniformOriginalEndpoint

theorem compFixed {State : Type*} {parameters : PhaseParameters} {budget : State → ℝ}
    {L ell : ℝ} {input middle output rank : ℕ}
    (operator : StartupSpatialAction rank middle output L ell) (fixed : operator.OriginalEndpointControlled parameters)
    {kernel : State → StartupL2 input →L[ℂ] StartupL2 middle}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension middle rank)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked) (nonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalEndpoint parameters budget (fun state => operator.signed.coarse.comp (kernel state))
      (fun state => operator.ranked.coarse.comp (ranked state)) :=
  (fixed.onBudget budget nonnegative).comp actual operator.ranked.bound operator.ranked.nonnegative
    (fun _ => operator.ranked.coarse_bound) nonnegative

/-- All literal variable rows, including the genuine force and its
average correction, retain the original core and one-high rank profile. -/
theorem actualRows {State : Type*} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0) (offset rank : ℕ)
    (four five : EstimateProfile)
    (fourFixed : ∀ grade,0≤four.fixed grade) (fourDeviation : ∀ grade,0≤four.deviation grade)
    (fiveFixed : ∀ grade,0≤five.fixed grade) (fiveDeviation : ∀ grade,0≤five.deviation grade)
    (baseField : State → ACore parameters 3) (rho curvature : State → ℝ)
    (data : State → LedgerData L parameters.sigma0 parameters.gamma ell) (coherent : ∀ state,LedgerCoherent (data state))
    (inverseCoherent : ∀ state,FamilyCoherent (determinantInverseFamily admissible (data state).gaugeDeviation))
    (fluxEstimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset four
      (data state).fluxDeviation (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3))
    (planarEstimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset five
      (data state).rotatedPlanarProduct (zeroFamily L parameters.sigma0 parameters.gamma ell 3 2))
    (thirdEstimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset five
      (data state).rotatedThirdProduct (zeroFamily L parameters.sigma0 parameters.gamma ell 3 1))
    (low : ∀ state,physicalBudget parameters (baseField state) (rho state) (curvature state) offset≤1)
    (currentControlled : StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalCurrentKernel admissible (data state).gaugeDeviation (coherent state).2.2.2.1 (inverseCoherent state))
      (fun state => (StartupRankOperator.current admissible rank (data state).gaugeDeviation (coherent state).2.2.2.1 (inverseCoherent state)).coarse)) :
    StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => startupGenuineForceKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.force admissible rank (data state) (coherent state) (inverseCoherent state)).coarse) ∧
    StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalThirdCorrectionKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.third admissible rank (data state) (coherent state) (inverseCoherent state)).coarse) ∧
    StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalFluxKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.flux admissible rank (data state) (coherent state) (inverseCoherent state)).coarse) ∧
    StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => startupGenuinePrincipalFluxKernel admissible (data state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.principalFlux admissible rank (data state) (coherent state) (inverseCoherent state)).coarse) := by
  let budget := fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank)
  have nonnegative (state : State) : 0≤budget state := add_nonneg zero_le_one
    (physicalBudget_nonnegative parameters (baseField state) (rho state) (curvature state) _)
  have planar := matrix (rank := rank) admissible lengthNonzero scaleNonzero offset five fiveFixed fiveDeviation
    baseField rho curvature (fun state => (data state).rotatedPlanarProduct) (fun _ => zeroFamily _ _ _ _ 3 2) planarEstimate low
  have planarCurrent := planar.comp currentControlled (startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma five)
    (startupMatrixProfileBaseBound_nonnegative admissible five fiveFixed fiveDeviation)
    (StartupUniformOriginalRank.matrix_rankBound admissible planarEstimate low) nonnegative
  have force := (compFixed (StartupSpatialAction.radial (L := L) (ell := ell) rank)
    (StartupSpatialAction.radial_originalEndpointControlled parameters rank) planarCurrent nonnegative).smul 2 nonnegative
  have third := matrix (rank := rank) admissible lengthNonzero scaleNonzero offset five fiveFixed fiveDeviation
    baseField rho curvature (fun state => (data state).rotatedThirdProduct) (fun _ => zeroFamily _ _ _ _ 3 1) thirdEstimate low
  have thirdCurrent := third.comp currentControlled (startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma five)
    (startupMatrixProfileBaseBound_nonnegative admissible five fiveFixed fiveDeviation)
    (StartupUniformOriginalRank.matrix_rankBound admissible thirdEstimate low) nonnegative
  have third := (compFixed (StartupSpatialAction.scalarMeanFree (L := L) (ell := ell) rank)
    (StartupSpatialAction.scalarMeanFree_originalEndpointControlled parameters rank) thirdCurrent nonnegative).smul 2 nonnegative
  have flux := matrix (rank := rank) admissible lengthNonzero scaleNonzero offset four fourFixed fourDeviation
    baseField rho curvature (fun state => (data state).fluxDeviation) (fun _ => zeroFamily _ _ _ _ 3 3) fluxEstimate low
  have flux := flux.comp currentControlled (startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma four)
    (startupMatrixProfileBaseBound_nonnegative admissible four fourFixed fourDeviation)
    (StartupUniformOriginalRank.matrix_rankBound admissible fluxEstimate low) nonnegative
  have planarFlux := compFixed (StartupSpatialAction.planarMeanFree (L := L) (ell := ell) rank)
    (StartupSpatialAction.planarMeanFree_originalEndpointControlled parameters rank)
    (compFixed (StartupSpatialAction.value (L := L) (ell := ell) rank planarPartMap) (StartupSpatialAction.value_originalEndpointControlled parameters rank planarPartMap) flux nonnegative) nonnegative
  have forceAverage := compFixed (StartupSpatialAction.average (L := L) (ell := ell) rank)
    (StartupSpatialAction.average_originalEndpointControlled parameters rank) force nonnegative
  have forceQuarter := compFixed (StartupSpatialAction.value (L := L) (ell := ell) rank quarterValueMap)
    (StartupSpatialAction.value_originalEndpointControlled parameters rank quarterValueMap) forceAverage nonnegative
  exact ⟨force,third,flux,planarFlux.sub (forceQuarter.smul (1/2) nonnegative)⟩

end StartupUniformOriginalEndpoint
end Grad.CartesianStartup
