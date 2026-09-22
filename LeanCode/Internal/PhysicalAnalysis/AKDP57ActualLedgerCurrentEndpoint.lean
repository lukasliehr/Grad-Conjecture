import AKDP56ActualPrincipalEndpointControl
import AKDP32ActualLedgerRankState

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupActualRankState

theorem current_endpoint (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (rank : ℕ) :
    StartupUniformOriginalEndpoint parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => originalCurrentKernel admissible state.ledger.val.gaugeDeviation state.ledger.property.1.2.2.2.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.current admissible rank state.ledger.val.gaugeDeviation state.ledger.property.1.2.2.2.1 state.inverseCoherent).coarse) := by
  have low : ∀ state : StartupActualRankState parameters admissible four five,
      physicalBudget parameters state.baseField state.rho state.epsilon 12≤1 := fun state => state.unit
  exact StartupUniformOriginalEndpoint.current
    (State := StartupActualRankState parameters admissible four five)
    parameters admissible lengthNonzero scaleNonzero 12 rank
    (unitProfile four) (unitProfile (complementExtensionConstant four))
    (fun _ => Nat.cast_nonneg _) fourNonnegative
    (fun _ => Nat.cast_nonneg _) (fun _ => abs_nonneg _)
    (fun state => state.baseField) (fun state => state.rho) (fun state => state.epsilon)
    (fun state => state.ledger.val.gaugeDeviation) (fun state => state.ledger.property.1.2.2.2.1) (fun state => state.inverseCoherent)
    (fun state => (current_profiles fourNonnegative state).1) (fun state => (current_profiles fourNonnegative state).2)
    low

end StartupActualRankState
end Grad.CartesianStartup
