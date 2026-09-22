import GC17Bounds

noncomputable section

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

/-- CT_GC17: the complete actual coefficient ledger on the prescribed AP27
B6 neighborhood, with one high original grade and no width loss. -/
theorem actualLedger : ActualLedgerGoal := by
  intro parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨ledgerLowRadius parameters L radius threshold,
    ledgerLowRadius_positive parameters positive radius thresholdPositive,
    ledgerLowRadius_le_one parameters L radius threshold,
    ledgerConstantFour parameters L radius, ledgerConstantFive parameters L,
    ledgerConstantFour_nonnegative parameters L radius, ledgerConstantFive_nonnegative parameters L, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
  have margins := actualInverseInput_margins parameters admissible radiusNonnegative thresholdPositive
    rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
  have lowFive : physicalBudget parameters field rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters field rho epsilon (by norm_num : 5 ≤ 6)).trans
      (low.trans (ledgerLowRadius_le_one parameters L radius threshold))
  refine ⟨physicalLedger parameters admissible rho alpha delta parameter epsilon field margins.2.1 margins.2.2,
    (primitiveSize_low_margin parameters admissible radiusNonnegative thresholdPositive
      rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low).1, ?_⟩
  exact physicalLedger_bounds parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field margins.1 lowFive margins.2.1 margins.2.2

end Grad.GaugeCoefficients.Physical.Ledger
