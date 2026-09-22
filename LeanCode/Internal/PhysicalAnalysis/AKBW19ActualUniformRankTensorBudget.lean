import AKBW18ActualUniformRankRows

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

def fixedTensorBudget : ℝ := 1 + ∑ outer : Fin 2, ∑ inner : Fin 2, ∑ row : Fin 3, (principalFixed 0 outer inner row).bound

def embeddingBudget : ℝ := 1 + (value 0 planarInclusionMap).bound + (value 0 toroidalInclusionMap).bound

def rowsBudget (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  forceBudget L sigma gamma four five + thirdBudget L sigma gamma four five + principalFluxBudget L sigma gamma four five

def principalBudget (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  3 * fixedTensorBudget * (embeddingBudget * rowsBudget L sigma gamma four five)

theorem fixedTensorBudget_nonnegative : 0 ≤ fixedTensorBudget := by
  unfold fixedTensorBudget
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun outer _ => Finset.sum_nonneg (fun inner _ =>
    Finset.sum_nonneg (fun row _ => (principalFixed 0 outer inner row).nonnegative))))

theorem embeddingBudget_nonnegative : 0 ≤ embeddingBudget := by
  unfold embeddingBudget
  positivity [(value 0 planarInclusionMap).nonnegative, (value 0 toroidalInclusionMap).nonnegative]

theorem rowsBudget_nonnegative (L sigma gamma : ℝ) (four five : ℕ → ℝ) :
    0 ≤ rowsBudget L sigma gamma four five := by
  have positive := rowBudgets_nonnegative L sigma gamma four five
  exact add_nonneg (add_nonneg positive.1 positive.2.1) positive.2.2.2

theorem principalBudget_nonnegative (L sigma gamma : ℝ) (four five : ℕ → ℝ) :
    0 ≤ principalBudget L sigma gamma four five := by
  unfold principalBudget
  positivity [fixedTensorBudget_nonnegative, embeddingBudget_nonnegative, rowsBudget_nonnegative L sigma gamma four five]

theorem principalFixed_le (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed rank outer inner row).bound ≤ fixedTensorBudget := by
  rw [principalFixed_bound_independent]
  have result := startupTripleSummand_le_sum
    (fun outer : Fin 2 => fun inner : Fin 2 => fun row : Fin 3 => (principalFixed 0 outer inner row).bound)
    (fun outer inner row => (principalFixed 0 outer inner row).nonnegative) outer inner row
  exact result.trans (le_add_of_nonneg_left zero_le_one)

variable {parameters : PhaseParameters} {L ell rho alpha delta parameter epsilon : ℝ}
    {base : ACore parameters 3} {admissible : Admissible L parameters.sigma0 parameters.gamma ell}

theorem actual_embeddedRow_bound (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade) (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (rank : ℕ) (row : Fin 3) :
    (embeddedRow admissible rank ledger.val ledger.property.1 inverseCoherent row).bound ≤
      (embeddingBudget * rowsBudget L parameters.sigma0 parameters.gamma four five) * physicalBudget parameters base rho epsilon 10 := by
  have rows := actual_row_bounds ledger four five fourNonnegative fiveNonnegative bounds unit small inverseCoherent rank
  have rowPositive := rowBudgets_nonnegative L parameters.sigma0 parameters.gamma four five
  have forceCap : forceBudget L parameters.sigma0 parameters.gamma four five ≤ rowsBudget L parameters.sigma0 parameters.gamma four five := by
    unfold rowsBudget
    linarith [rowPositive.2.1, rowPositive.2.2.2]
  have thirdCap : thirdBudget L parameters.sigma0 parameters.gamma four five ≤ rowsBudget L parameters.sigma0 parameters.gamma four five := by
    unfold rowsBudget
    linarith [rowPositive.1, rowPositive.2.2.2]
  have fluxCap : principalFluxBudget L parameters.sigma0 parameters.gamma four five ≤ rowsBudget L parameters.sigma0 parameters.gamma four five := by
    unfold rowsBudget
    linarith [rowPositive.1, rowPositive.2.1]
  have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
  have planarCap : (value rank planarInclusionMap).bound ≤ embeddingBudget := by
    change (value 0 planarInclusionMap).bound ≤ _
    unfold embeddingBudget
    linarith [(value 0 toroidalInclusionMap).nonnegative]
  have toroidalCap : (value rank toroidalInclusionMap).bound ≤ embeddingBudget := by
    change (value 0 toroidalInclusionMap).bound ≤ _
    unfold embeddingBudget
    linarith [(value 0 planarInclusionMap).nonnegative]
  fin_cases row
  · change (value rank planarInclusionMap).bound * (force admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤ _
    exact (mul_le_mul planarCap (rows.1.trans (mul_le_mul_of_nonneg_right forceCap budgetPositive))
      (force admissible rank ledger.val ledger.property.1 inverseCoherent).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)
  · change (value rank toroidalInclusionMap).bound * (third admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤ _
    exact (mul_le_mul toroidalCap (rows.2.1.trans (mul_le_mul_of_nonneg_right thirdCap budgetPositive))
      (third admissible rank ledger.val ledger.property.1 inverseCoherent).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)
  · change (value rank planarInclusionMap).bound * (principalFlux admissible rank ledger.val ledger.property.1 inverseCoherent).bound ≤ _
    exact (mul_le_mul planarCap (rows.2.2.2.trans (mul_le_mul_of_nonneg_right fluxCap budgetPositive))
      (principalFlux admissible rank ledger.val ledger.property.1 inverseCoherent).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)

/-- Original B10 controls the entire actual principal tensor simultaneously
for every derivative rank. All native coefficients are the SAME ledger. -/
theorem actual_principalTensor_bound (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade) (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (rank : ℕ) (outer inner : Fin 2) :
    (principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent outer inner).bound ≤
      principalBudget L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
  have entryBound (row : Fin 3) := mul_le_mul (principalFixed_le rank outer inner row)
    (actual_embeddedRow_bound ledger four five fourNonnegative fiveNonnegative bounds unit small inverseCoherent rank row)
    (embeddedRow admissible rank ledger.val ledger.property.1 inverseCoherent row).nonnegative fixedTensorBudget_nonnegative
  change ((principalFixed rank outer inner 0).bound * (embeddedRow admissible rank ledger.val ledger.property.1 inverseCoherent 0).bound +
    (principalFixed rank outer inner 1).bound * (embeddedRow admissible rank ledger.val ledger.property.1 inverseCoherent 1).bound) +
    (principalFixed rank outer inner 2).bound * (embeddedRow admissible rank ledger.val ledger.property.1 inverseCoherent 2).bound ≤ _
  exact (add_le_add (add_le_add (entryBound 0) (entryBound 1)) (entryBound 2)).trans_eq (by unfold principalBudget; ring)

end StartupRankOperator
end Grad.CartesianStartup
