import AKAL4ActualRowNormBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- A scalar payment independent of ell, fields and cell order. Absolute
 values allow the neighborhood to be selected before any admissible scale. -/
def startupActualRowsConstant (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  |startupForceBound L sigma gamma four five| + |startupThirdBound L sigma gamma four five| +
    |startupFluxBound L sigma gamma four| + |startupPrincipalFluxBound L sigma gamma four five|

theorem startupActualRowsConstant_nonnegative (L sigma gamma : ℝ) (four five : ℕ → ℝ) :
    0 ≤ startupActualRowsConstant L sigma gamma four five := by
  unfold startupActualRowsConstant
  positivity

variable {L ell : ℝ} {parameters : PhaseParameters}
  {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
  {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}

/-- Smallness concerns the literal actual full-current ER11 coefficients
 on both inherited carriers. It makes no claim of a rough PDE or tensor
 factorization; those are distinct downstream obligations. -/
def ActualStartupRowsSmall
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) : Prop :=
  ‖originalForceCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalThirdCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalPrincipalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalForceCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalThirdCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold ∧
  ‖originalPrincipalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ < threshold

theorem actualStartupRowsSmall_of_budget
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ)
    (low : physicalBudget parameters base rho epsilon 10 <
      threshold / (startupActualRowsConstant L parameters.sigma0 parameters.gamma four five + 1)) :
    ActualStartupRowsSmall ledger inverseCoherent threshold := by
  have coarse := startupActualRows_Kernel_bounds ledger four five fourNonnegative fiveNonnegative bounds unit small inverseCoherent
  have fine := startupActualRows_FirstGraph_bounds ledger four five fourNonnegative fiveNonnegative bounds unit small inverseCoherent
  have nonnegative := startupActualRowsConstant_nonnegative L parameters.sigma0 parameters.gamma four five
  have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
  have positive : 0 < startupActualRowsConstant L parameters.sigma0 parameters.gamma four five + 1 := by positivity
  have product := (lt_div_iff₀ positive).mp low
  have paid : startupActualRowsConstant L parameters.sigma0 parameters.gamma four five *
      physicalBudget parameters base rho epsilon 10 < threshold := by nlinarith
  have a : startupForceBound L parameters.sigma0 parameters.gamma four five ≤
      startupActualRowsConstant L parameters.sigma0 parameters.gamma four five := by
    unfold startupActualRowsConstant
    linarith [le_abs_self (startupForceBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupThirdBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupFluxBound L parameters.sigma0 parameters.gamma four),
      abs_nonneg (startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five)]
  have c : startupThirdBound L parameters.sigma0 parameters.gamma four five ≤
      startupActualRowsConstant L parameters.sigma0 parameters.gamma four five := by
    unfold startupActualRowsConstant
    linarith [le_abs_self (startupThirdBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupForceBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupFluxBound L parameters.sigma0 parameters.gamma four),
      abs_nonneg (startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five)]
  have h : startupFluxBound L parameters.sigma0 parameters.gamma four ≤
      startupActualRowsConstant L parameters.sigma0 parameters.gamma four five := by
    unfold startupActualRowsConstant
    linarith [le_abs_self (startupFluxBound L parameters.sigma0 parameters.gamma four),
      abs_nonneg (startupForceBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupThirdBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five)]
  have s : startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five ≤
      startupActualRowsConstant L parameters.sigma0 parameters.gamma four five := by
    unfold startupActualRowsConstant
    linarith [le_abs_self (startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupForceBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupThirdBound L parameters.sigma0 parameters.gamma four five),
      abs_nonneg (startupFluxBound L parameters.sigma0 parameters.gamma four)]
  have ca := (mul_le_mul_of_nonneg_right a budgetPositive).trans_lt paid
  have cc := (mul_le_mul_of_nonneg_right c budgetPositive).trans_lt paid
  have ch := (mul_le_mul_of_nonneg_right h budgetPositive).trans_lt paid
  have cs := (mul_le_mul_of_nonneg_right s budgetPositive).trans_lt paid
  exact ⟨coarse.2.1.trans_lt ca, coarse.2.2.1.trans_lt cc, coarse.2.2.2.1.trans_lt ch,
    coarse.2.2.2.2.trans_lt cs, fine.2.1.trans_lt ca, fine.2.2.1.trans_lt cc,
    fine.2.2.2.1.trans_lt ch, fine.2.2.2.2.trans_lt cs⟩

end Grad.CartesianStartup
