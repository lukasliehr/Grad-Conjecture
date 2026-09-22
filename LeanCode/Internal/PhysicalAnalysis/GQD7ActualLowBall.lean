import GQD6CompletedIsomorphism

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- CT_GC23 on the SAME single physical low ball as the actual smooth
transfer, all original cells, widths, scales, seeds and grades. -/
def ActualCompensatedClosureGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∀ (ell rho alpha delta parameter epsilon : ℝ)
      (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
      |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
      ∀ base : ACore parameters 3,
        physicalBudget parameters base rho epsilon 10 < lowRadius →
        physicalBudget parameters base rho epsilon 12 ≤ 1 →
        ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
          primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
          ∃ smooth : SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation,
            ∀ grade : ℕ, 3 ≤ grade → Nonempty (CompletedCompensatedIsomorphism smooth grade)

theorem actualCompensatedClosure (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualCompensatedClosureGoal parameters L radius threshold := by
  obtain ⟨lowRadius, positiveRadius, radiusOne, supplied⟩ :=
    actualCompensatedCore parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, positiveRadius, radiusOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  obtain ⟨ledger, margin, ⟨smooth⟩⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  exact ⟨ledger, margin, smooth, fun grade large => ⟨completedCompensatedIsomorphism smooth grade large⟩⟩

end Grad.GaugeCoefficients.Physical.Compensated
