import GQF43ActualForwardComparison

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Universal actual-state consumer: no ledger, transfer, forward map, or
range record is an input. The constructor supplies them all; this theorem
then applies their exact core, range, four-row difference and norm laws. -/
theorem actualForwardComparisonConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ (primitivePolynomials budgetPolynomials : ℕ → Polynomial ℝ) (referenceBound : ℕ → ℝ),
      ComparisonPolynomialContract primitivePolynomials ∧ ComparisonPolynomialContract budgetPolynomials ∧
      (∀ grade, 0 ≤ referenceBound grade) ∧
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
                SmoothForwardComparison admissible ledger.val ledger.property.1 smooth ∧
                ∀ grade (large : 3 ≤ grade),
                  ∃ realization : CompletedForwardComparison admissible ledger.val ledger.property.1 smooth grade large,
                    (∀ core, realization.circle (compensatedIntoClosure admissible grade _ core) =
                      circularAugmentedCore admissible grade core.val) ∧
                    (∀ core, realization.current (compensatedIntoClosure admissible grade _ core) =
                      actualAugmentedCore admissible ledger.val ledger.property.1 grade core.val) ∧
                    (∀ field,
                      capAugmentedRange admissible grade (realization.circle field) ∧
                      capAugmentedRange admissible grade (realization.current (completedTransfer smooth grade large field)) ∧
                      realization.current (completedTransfer smooth grade large field) - realization.circle field =
                        realization.error (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible
                          ledger.val.gaugeDeviation (grade + 1)
                          (completedReconstruct admissible grade (circularCompensatedCore admissible) field))) ∧
                    ‖realization.circle‖ ≤ referenceBound grade ∧
                    ‖realization.current.comp (completedTransfer smooth grade large) - realization.circle‖ ≤
                      (primitivePolynomials grade).eval
                        (primitiveSize parameters admissible rho alpha delta parameter epsilon base (grade + 3)) ∧
                    ‖realization.current.comp (completedTransfer smooth grade large) - realization.circle‖ ≤
                      (budgetPolynomials grade).eval (physicalBudget parameters base rho epsilon (grade + 7)) := by
  have result := actualForwardComparison parameters L radius threshold positive radiusNonnegative thresholdPositive
  let primitive := result.choose
  have second := result.choose_spec
  let budget := second.choose
  have third := second.choose_spec
  let reference := third.choose
  have contracts := third.choose_spec
  let lowRadius := contracts.2.2.2.choose
  have neighborhood := contracts.2.2.2.choose_spec
  refine ⟨primitive, budget, reference, contracts.1, contracts.2.1, contracts.2.2.1,
    lowRadius, neighborhood.1, neighborhood.2.1, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  have supplied := neighborhood.2.2 ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  let ledger := supplied.choose
  have state := supplied.choose_spec
  let smooth := state.2.2.choose
  have transferred := state.2.2.choose_spec
  refine ⟨ledger, state.1, state.2.1, smooth, transferred.1, ?_⟩
  intro grade large
  have completed := transferred.2 grade large
  let realization := completed.choose
  have bounds := completed.choose_spec
  exact ⟨realization, realization.circleCore, realization.currentCore,
    fun field => ⟨realization.circleRange field,
      realization.currentRange (completedTransfer smooth grade large field), realization.difference field⟩,
    bounds.1, bounds.2.1, bounds.2.2⟩

end Grad.GaugeCoefficients.Physical.Compensated
