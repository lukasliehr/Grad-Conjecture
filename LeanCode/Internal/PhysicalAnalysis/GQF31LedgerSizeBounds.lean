import GQF24ErrorBounds

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Neumann.Regularity

theorem gaugeBlockNorm_le_norm {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3)
    (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (outerSmall : ‖outer‖ ≤ 1) (innerSmall : ‖inner‖ ≤ 1) :
    gaugeBlockNorm coefficient outer inner ≤ ‖coefficient‖ := by
  have normFormula : ‖coefficient‖ =
      ∑ index : DerivativeIndex grade, ∑' cell : ℤ, ‖weightedDerivative coefficient cell index‖ := by
    rw [coefficient_norm_formula]
    exact Summable.tsum_finsetSum (fun index _ => coordinate_norm_summable coefficient.val index)
  rw [normFormula]
  exact Finset.sum_le_sum (fun index _ =>
    (gaugeBlockNorm_summable coefficient outer inner outerSmall innerSmall index).tsum_le_tsum
      (fun cell => operatorBlockMap_norm_le outer inner _ outerSmall innerSmall)
      (coordinate_norm_summable coefficient.val index))

theorem gaugeEpsilon_le_four_norm {L sigma gamma ell : ℝ} {grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3) :
    gaugeEpsilon coefficient ≤ 4 * ‖coefficient‖ := by
  have first := gaugeBlockNorm_le_norm coefficient planarPartMap planarInclusionMap
    planarPartMap_norm_le planarInclusionMap_norm_le
  have second := gaugeBlockNorm_le_norm coefficient planarPartMap toroidalInclusionMap
    planarPartMap_norm_le toroidalInclusionMap_norm_le
  have third := gaugeBlockNorm_le_norm coefficient toroidalPartMap planarInclusionMap
    toroidalPartMap_norm_le planarInclusionMap_norm_le
  have fourth := gaugeBlockNorm_le_norm coefficient toroidalPartMap toroidalInclusionMap
    toroidalPartMap_norm_le toroidalInclusionMap_norm_le
  unfold gaugeEpsilon
  linarith

theorem errorCoefficientSize_le_ledger {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base) (grade : ℕ) :
    errorCoefficientSize ledger.val grade ≤ ledgerSizeFour ledger grade + ledgerSizeFive ledger grade := by
  unfold errorCoefficientSize ledgerSizeFour ledgerSizeFive
  linarith [norm_nonneg (ledger.val.inverseTransposeDeviation grade),
    norm_nonneg (ledger.val.seedInverse grade - gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2),
    norm_nonneg (ledger.val.gaugeDeviation grade), norm_nonneg (ledger.val.rotatedFrame grade)]

theorem gaugeCoefficientSize_le_ledger {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base) (grade : ℕ) :
    gaugeEpsilon (ledger.val.gaugeDeviation grade) ≤ 4 * ledgerSizeFour ledger grade := by
  apply (gaugeEpsilon_le_four_norm _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold ledgerSizeFour
  linarith [norm_nonneg (ledger.val.inverseTransposeDeviation grade),
    norm_nonneg (ledger.val.seedInverse grade - gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2),
    norm_nonneg (ledger.val.fluxDeviation grade), norm_nonneg (ledger.val.traceDeviation grade)]

theorem actualErrorSize_budget {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade) (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5)) (grade : ℕ) :
    errorCoefficientSize ledger.val (grade + 1) ≤
      (four (grade + 1) + five (grade + 1)) * physicalBudget parameters base rho epsilon (grade + 7) := by
  exact (errorCoefficientSize_le_ledger ledger (grade + 1)).trans
    ((add_le_add ((bounds (grade + 1)).1.trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters base rho epsilon (by omega)) (fourNonnegative _)))
      ((bounds (grade + 1)).2.trans
        (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters base rho epsilon (by omega)) (fiveNonnegative _)))).trans_eq
          (add_mul _ _ _).symm)

theorem actualGaugeSize_budget {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four : ℕ → ℝ)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4))
    (grade : ℕ) :
    gaugeEpsilon (ledger.val.gaugeDeviation (grade + 3)) ≤
      (4 * four (grade + 3)) * physicalBudget parameters base rho epsilon (grade + 7) :=
  (gaugeCoefficientSize_le_ledger ledger (grade + 3)).trans
    ((mul_le_mul_of_nonneg_left (bounds (grade + 3)) (by norm_num)).trans_eq (by ring))

end Grad.GaugeCoefficients.Physical.Compensated
