import AKBW17ActualUniformRankMatrixBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRankOperator

def forceBudget (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  2 * ((radial 0).bound * ((2 * |startupDeviationMatrixConstant L sigma gamma five|) * currentBudget L sigma gamma four))

def thirdBudget (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  2 * ((scalarMeanFree 0).bound * ((2 * |startupDeviationMatrixConstant L sigma gamma five|) * currentBudget L sigma gamma four))

def fluxBudget (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  (2 * |startupDeviationMatrixConstant L sigma gamma four|) * currentBudget L sigma gamma four

def principalFluxBudget (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  (planarMeanFree 0).bound * ((value 0 planarPartMap).bound * fluxBudget L sigma gamma four) +
    ‖(1 / 2 : ℂ)‖ * ((value 0 quarterValueMap).bound * ((average 0).bound * forceBudget L sigma gamma four five))

theorem rowBudgets_nonnegative (L sigma gamma : ℝ) (four five : ℕ → ℝ) :
    0 ≤ forceBudget L sigma gamma four five ∧ 0 ≤ thirdBudget L sigma gamma four five ∧
      0 ≤ fluxBudget L sigma gamma four ∧ 0 ≤ principalFluxBudget L sigma gamma four five := by
  have forcePositive : 0 ≤ forceBudget L sigma gamma four five := by
    unfold forceBudget
    positivity [(radial 0).nonnegative, currentBudget_nonnegative L sigma gamma four]
  have thirdPositive : 0 ≤ thirdBudget L sigma gamma four five := by
    unfold thirdBudget
    positivity [(scalarMeanFree 0).nonnegative, currentBudget_nonnegative L sigma gamma four]
  have fluxPositive : 0 ≤ fluxBudget L sigma gamma four := by
    unfold fluxBudget
    positivity [currentBudget_nonnegative L sigma gamma four]
  refine ⟨forcePositive, thirdPositive, fluxPositive, ?_⟩
  unfold principalFluxBudget
  positivity [(planarMeanFree 0).nonnegative, (value 0 planarPartMap).nonnegative,
    (value 0 quarterValueMap).nonnegative, (average 0).nonnegative]

variable {parameters : PhaseParameters} {L ell rho alpha delta parameter epsilon : ℝ}
    {base : ACore parameters 3} {admissible : Admissible L parameters.sigma0 parameters.gamma ell}

theorem actual_row_bounds (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade) (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) (rank : ℕ) :
    (force admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
        forceBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    (third admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
        thirdBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    (flux admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
        fluxBudget L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 ∧
    (principalFlux admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
        principalFluxBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
  have currentBound := actual_current_bound ledger four fourNonnegative (fun grade => (bounds grade).1) unit small inverseCoherent rank
  have deviation := actual_deviation_bounds ledger four five fourNonnegative fiveNonnegative bounds rank
  have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
  have currentPositive := (current admissible rank ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent).nonnegative
  have forceBound : (force admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
      forceBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    change ‖(2 : ℂ)‖ * ((radial 0).bound *
      ((matrix admissible rank ledger.val.rotatedPlanarProduct ledger.property.1.2.2.2.2.2.2.2.1).bound *
      (current admissible rank ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent).bound)) ≤ _
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    unfold forceBudget
    have productBound := mul_le_mul deviation.1 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound (radial 0).nonnegative)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have thirdBound : (third admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
      thirdBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    change ‖(2 : ℂ)‖ * ((scalarMeanFree 0).bound *
      ((matrix admissible rank ledger.val.rotatedThirdProduct ledger.property.1.2.2.2.2.2.2.2.2).bound *
      (current admissible rank ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent).bound)) ≤ _
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    unfold thirdBudget
    have productBound := mul_le_mul deviation.2.1 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound (scalarMeanFree 0).nonnegative)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have fluxBound : (flux admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤
      fluxBudget L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 := by
    change (matrix admissible rank ledger.val.fluxDeviation ledger.property.1.2.2.2.2.1).bound *
      (current admissible rank ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent).bound ≤ _
    unfold fluxBudget
    exact (mul_le_mul deviation.2.2 currentBound currentPositive (mul_nonneg (by positivity) budgetPositive)).trans_eq (by ring)
  refine ⟨forceBound, thirdBound, fluxBound, ?_⟩
  change (planarMeanFree 0).bound * ((value 0 planarPartMap).bound *
    (flux admissible rank ledger.val ledger.property.1 inverseCoherent).bound) +
    ‖(1 / 2 : ℂ)‖ * ((value 0 quarterValueMap).bound * ((average 0).bound *
      (force admissible rank ledger.val ledger.property.1 inverseCoherent).bound)) ≤ _
  have first := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fluxBound (value 0 planarPartMap).nonnegative)
    (planarMeanFree 0).nonnegative
  have second := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left forceBound
    (average 0).nonnegative) (value 0 quarterValueMap).nonnegative) (norm_nonneg (1 / 2 : ℂ))
  exact (add_le_add first second).trans_eq (by unfold principalFluxBudget; ring)

end StartupRankOperator
end Grad.CartesianStartup
