import AKDS36OriginalUnitRankBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.CartesianStartup.StartupRankOperator
variable {parameters : PhaseParameters} {length radius : ℝ}

/-- All original force/third/flux operator bounds are linear in one B10,
with constants independent of covector rank. -/
theorem row_bounds (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) (rank : ℕ) :
    (force (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative)
      (state.inverseCoherent radiusNonnegative)).bound≤
      forceBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length)*
        physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    (third (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative)
      (state.inverseCoherent radiusNonnegative)).bound≤
      thirdBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length)*
        physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    (flux (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative)
      (state.inverseCoherent radiusNonnegative)).bound≤
      fluxBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius)*
        physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    (principalFlux (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative)
      (state.inverseCoherent radiusNonnegative)).bound≤
      principalFluxBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length)*
        physicalBudget parameters state.field state.rho state.epsilon 10 := by
  let L : ℝ := 1
  let admissible := unitDiskAdmissible parameters
  let base := state.field
  let rho := state.rho
  let epsilon := state.epsilon
  let four := originalUnitFour parameters length radius
  let five := originalUnitFive parameters length
  let inverseCoherent := state.inverseCoherent radiusNonnegative
  have currentBound := state.current_bound radiusNonnegative rank
  have deviation := state.deviation_bounds radiusNonnegative rank
  have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
  have currentPositive := (current admissible rank state.data.gaugeDeviation (state.coherent radiusNonnegative).2.2.2.1 inverseCoherent).nonnegative
  have forceBound : (force admissible rank state.data (state.coherent radiusNonnegative) inverseCoherent).bound ≤
      forceBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    change ‖(2 : ℂ)‖ * ((radial 0).bound *
      ((matrix admissible rank state.data.rotatedPlanarProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.1).bound *
      (current admissible rank state.data.gaugeDeviation (state.coherent radiusNonnegative).2.2.2.1 inverseCoherent).bound)) ≤ _
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    unfold forceBudget
    have productBound := mul_le_mul deviation.1 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound (radial 0).nonnegative)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have thirdBound : (third admissible rank state.data (state.coherent radiusNonnegative) inverseCoherent).bound ≤
      thirdBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    change ‖(2 : ℂ)‖ * ((scalarMeanFree 0).bound *
      ((matrix admissible rank state.data.rotatedThirdProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.2).bound *
      (current admissible rank state.data.gaugeDeviation (state.coherent radiusNonnegative).2.2.2.1 inverseCoherent).bound)) ≤ _
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    unfold thirdBudget
    have productBound := mul_le_mul deviation.2.1 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound (scalarMeanFree 0).nonnegative)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have fluxBound : (flux admissible rank state.data (state.coherent radiusNonnegative) inverseCoherent).bound ≤
      fluxBudget L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 := by
    change (matrix admissible rank state.data.fluxDeviation (state.coherent radiusNonnegative).2.2.2.2.1).bound *
      (current admissible rank state.data.gaugeDeviation (state.coherent radiusNonnegative).2.2.2.1 inverseCoherent).bound ≤ _
    unfold fluxBudget
    exact (mul_le_mul deviation.2.2 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)).trans_eq (by ring)
  refine ⟨forceBound, thirdBound, fluxBound, ?_⟩
  change (planarMeanFree 0).bound * ((value 0 planarPartMap).bound *
    (flux admissible rank state.data (state.coherent radiusNonnegative) inverseCoherent).bound) +
    ‖(1 / 2 : ℂ)‖ * ((value 0 quarterValueMap).bound * ((average 0).bound *
      (force admissible rank state.data (state.coherent radiusNonnegative) inverseCoherent).bound)) ≤ _
  have first := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fluxBound (value 0 planarPartMap).nonnegative)
    (planarMeanFree 0).nonnegative
  have second := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left forceBound
    (average 0).nonnegative) (value 0 quarterValueMap).nonnegative) (norm_nonneg (1 / 2 : ℂ))
  exact (add_le_add first second).trans_eq (by unfold principalFluxBudget; ring)

end Grad.OriginalCoreRealization.OriginalUnitRankState
