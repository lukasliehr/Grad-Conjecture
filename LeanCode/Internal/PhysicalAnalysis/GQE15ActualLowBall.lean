import GQE14ScalarTraceContract

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- CT_GC24 retains the exact same physical low neighborhood as GC22/23:
one B10-small, B12-bounded ball, all cells and all admitted scales/seeds. -/
def ActualScalarTraceGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
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
            ScalarTracePreservation admissible ledger.val smooth ∧
            ∀ grade : ℕ, 3 ≤ grade → Nonempty (CompletedCompensatedIsomorphism smooth grade)

theorem actualScalarTracePreservation (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualScalarTraceGoal parameters L radius threshold := by
  obtain ⟨lowRadius, positiveRadius, boundedRadius, supplied⟩ :=
    actualCompensatedClosure parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, positiveRadius, boundedRadius, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  obtain ⟨ledger, margin, smooth, completed⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  exact ⟨ledger, margin, smooth, scalarTracePreservation admissible ledger.val smooth, completed⟩

/-- Actual downstream constructor, not a conditional assumption of the
missing contraction or preservation laws. -/
theorem actualScalarTraceConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualScalarTraceGoal parameters L radius threshold :=
  actualScalarTracePreservation parameters L radius threshold positive radiusNonnegative thresholdPositive

end Grad.GaugeCoefficients.Physical.Compensated
