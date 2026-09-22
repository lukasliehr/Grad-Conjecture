import GQF21ActualSourceRange

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- Actual-state consumer of the smooth comparison. Both the ledger and
the compensated isomorphism are constructed from the original low ball;
no missing inverse or source-range record is a premise. Quantitative
completed forward comparison is proved in the subsequent suffix. -/
theorem actualSmoothComparison (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          physicalBudget parameters base rho epsilon 12 ≤ 1 →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ComplementCancellationGoal admissible ∧
            ∃ smooth : SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation,
              SmoothForwardComparison admissible ledger.val ledger.property.1 smooth := by
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ :=
    actualCompensatedCore parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  obtain ⟨ledger, margin, ⟨smooth⟩⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  exact ⟨ledger, margin, actualComplementCancellation admissible, smooth,
    actualSmoothForwardComparison admissible ledger.val ledger.property.1 smooth⟩

end Grad.GaugeCoefficients.Physical.Compensated
