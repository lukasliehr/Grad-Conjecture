import AKDP32ActualLedgerRankState

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupActualRankState

/-- Actual retained ledger bounds discharge every variable-row profile.
No operator derivative or intermediate core estimate is an assumption. -/
theorem rows_controlled (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade) (rank : ℕ) :
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => startupGenuineForceKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.force admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent).coarse) ∧
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => originalThirdCorrectionKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.third admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent).coarse) ∧
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => originalFluxKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.flux admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent).coarse) ∧
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => startupGenuinePrincipalFluxKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.principalFlux admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent).coarse) := by
  have profiles (state : StartupActualRankState parameters admissible four five) :=
    startupActualLedger_deviationProfiles state.ledger four five fourNonnegative fiveNonnegative state.bounds
  have low : ∀ state : StartupActualRankState parameters admissible four five,
      physicalBudget parameters state.baseField state.rho state.epsilon 12≤1 := fun state => state.unit
  exact StartupUniformOriginalRank.actualRows
    (State := StartupActualRankState parameters admissible four five)
    parameters admissible lengthNonzero scaleNonzero 12 rank
    (startupDeviationProfile four) (startupDeviationProfile five) (fun _ => le_rfl) fourNonnegative (fun _ => le_rfl) fiveNonnegative
    (fun state => state.baseField) (fun state => state.rho) (fun state => state.epsilon)
    (fun state => state.ledger.val) (fun state => state.ledger.property.1) (fun state => state.inverseCoherent)
    (fun state => (profiles state).2.1) (fun state => (profiles state).2.2.1) (fun state => (profiles state).2.2.2)
    low (current_controlled parameters admissible lengthNonzero scaleNonzero four five fourNonnegative rank)

/-- The complete SAME actual principal tensor now has its uniform
one-high rank profile from the original ledger alone. -/
theorem principal_controlled (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade)
    (rank : ℕ) (outer inner : Fin 2) :
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => startupGenuinePrincipalTensorKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner)
      (fun state => (StartupRankOperator.principalTensor admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner).coarse) := by
  have rows := rows_controlled parameters admissible lengthNonzero scaleNonzero four five fourNonnegative fiveNonnegative rank
  exact StartupUniformOriginalRank.actualPrincipal
    (State := StartupActualRankState parameters admissible four five)
    admissible rank (budget rank) (budget_nonnegative rank)
    (fun state => state.ledger.val) (fun state => state.ledger.property.1) (fun state => state.inverseCoherent)
    rows.1 rows.2.1 rows.2.2.2 outer inner

end StartupActualRankState
end Grad.CartesianStartup
