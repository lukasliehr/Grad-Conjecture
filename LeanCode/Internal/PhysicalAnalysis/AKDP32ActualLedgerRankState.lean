import AKDP31ActualPrincipalOriginalRankControl

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Use the existing dependent-pair carrier; no generated recursor
unfolds the full actual ledger fidelity predicate. -/
def StartupActualRankData (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) :=
  Σ state : ℝ × ℝ × ℝ × ℝ × ℝ × ACore parameters 3,
    ActualLedger parameters admissible state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2.1 state.2.2.2.2.2

namespace StartupActualRankData
variable {parameters : PhaseParameters} {L ell : ℝ} {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
abbrev rho (state : StartupActualRankData parameters admissible) := state.1.1
abbrev alpha (state : StartupActualRankData parameters admissible) := state.1.2.1
abbrev delta (state : StartupActualRankData parameters admissible) := state.1.2.2.1
abbrev parameter (state : StartupActualRankData parameters admissible) := state.1.2.2.2.1
abbrev epsilon (state : StartupActualRankData parameters admissible) := state.1.2.2.2.2.1
abbrev baseField (state : StartupActualRankData parameters admissible) := state.1.2.2.2.2.2
abbrev ledger (state : StartupActualRankData parameters admissible) := state.2
end StartupActualRankData

def StartupActualRankState (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (four five : ℕ → ℝ) :=
  { state : StartupActualRankData parameters admissible //
    FamilyCoherent (determinantInverseFamily admissible state.ledger.val.gaugeDeviation) ∧
    (∀ grade,ledgerSizeFour state.ledger grade≤four grade*physicalBudget parameters state.baseField state.rho state.epsilon (grade+4) ∧
      ledgerSizeFive state.ledger grade≤five grade*physicalBudget parameters state.baseField state.rho state.epsilon (grade+5)) ∧
    physicalBudget parameters state.baseField state.rho state.epsilon 12≤1 ∧
    physicalBudget parameters state.baseField state.rho state.epsilon 6≤determinantLowRadius four }

namespace StartupActualRankState
variable {parameters : PhaseParameters} {L ell : ℝ} {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {four five : ℕ → ℝ}

abbrev rho (state : StartupActualRankState parameters admissible four five) := state.val.rho
abbrev alpha (state : StartupActualRankState parameters admissible four five) := state.val.alpha
abbrev delta (state : StartupActualRankState parameters admissible four five) := state.val.delta
abbrev parameter (state : StartupActualRankState parameters admissible four five) := state.val.parameter
abbrev epsilon (state : StartupActualRankState parameters admissible four five) := state.val.epsilon
abbrev baseField (state : StartupActualRankState parameters admissible four five) := state.val.baseField
abbrev ledger (state : StartupActualRankState parameters admissible four five) := state.val.ledger
abbrev inverseCoherent (state : StartupActualRankState parameters admissible four five) := state.property.1
abbrev bounds (state : StartupActualRankState parameters admissible four five) := state.property.2.1
abbrev unit (state : StartupActualRankState parameters admissible four five) := state.property.2.2.1
abbrev small (state : StartupActualRankState parameters admissible four five) := state.property.2.2.2

def budget (rank : ℕ) (state : StartupActualRankState parameters admissible four five) : ℝ :=
  1+physicalBudget parameters state.baseField state.rho state.epsilon (12+rank)

theorem budget_nonnegative (rank : ℕ) (state : StartupActualRankState parameters admissible four five) :
    0≤budget rank state := add_nonneg zero_le_one (physicalBudget_nonnegative parameters state.baseField state.rho state.epsilon _)

theorem current_profiles (fourNonnegative : ∀ grade,0≤four grade) (state : StartupActualRankState parameters admissible four five) :
    FamilyEstimate parameters state.baseField state.rho state.epsilon 12 (unitProfile four)
      (fullGaugeFamily state.ledger.val.gaugeDeviation) (identityFamily L parameters.sigma0 parameters.gamma ell 3) ∧
    FamilyEstimate parameters state.baseField state.rho state.epsilon 12 (unitProfile (complementExtensionConstant four))
      (complementExtensionFamily admissible state.ledger.val.gaugeDeviation) (identityFamily L parameters.sigma0 parameters.gamma ell 3) := by
  apply startupCurrent_actualProfiles parameters admissible state.baseField state.ledger.val.gaugeDeviation
    state.ledger.property.1.2.2.2.1 state.inverseCoherent four fourNonnegative
    ((physicalBudget_monotone parameters state.baseField state.rho state.epsilon (by norm_num : 6≤12)).trans state.unit)
  · intro grade
    exact (actualGaugeDeviation_bound state.ledger grade).trans (state.bounds grade).1
  · exact state.small

theorem current_controlled (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (rank : ℕ) :
    StartupUniformOriginalRank parameters (budget (parameters := parameters) (admissible := admissible) (four := four) (five := five) rank)
      (fun state => originalCurrentKernel admissible state.ledger.val.gaugeDeviation state.ledger.property.1.2.2.2.1 state.inverseCoherent)
      (fun state => (StartupRankOperator.current admissible rank state.ledger.val.gaugeDeviation state.ledger.property.1.2.2.2.1 state.inverseCoherent).coarse) := by
  have low : ∀ state : StartupActualRankState parameters admissible four five,
      physicalBudget parameters state.baseField state.rho state.epsilon 12≤1 := fun state => state.unit
  exact StartupUniformOriginalRank.current
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
