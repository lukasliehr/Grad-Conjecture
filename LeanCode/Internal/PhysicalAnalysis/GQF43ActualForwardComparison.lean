import GQF42CanonicalLowBall

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

def primitiveForwardPolynomial (L sigma gamma : ℝ) (grade : ℕ) : Polynomial ℝ :=
  forwardComparisonPolynomial L sigma gamma grade (errorPrimitivePolynomial (grade + 1)) (gaugePrimitivePolynomial (grade + 3))

def budgetForwardPolynomial (parameters : PhaseParameters) (L radius : ℝ) (grade : ℕ) : Polynomial ℝ :=
  forwardComparisonPolynomial L parameters.sigma0 parameters.gamma grade
    (linearBoundPolynomial (ledgerConstantFour parameters L radius (grade + 1) + ledgerConstantFive parameters L (grade + 1)))
    (linearBoundPolynomial (4 * ledgerConstantFour parameters L radius (grade + 3)))

theorem primitiveForwardPolynomial_contract {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : ComparisonPolynomialContract (primitiveForwardPolynomial L sigma gamma) :=
  comparisonPolynomialContract_of_nonnegative_zero _
    (fun grade => forwardComparisonPolynomial_nonnegative admissible grade
      (errorPrimitivePolynomial_nonnegative (grade + 1)) (gaugePrimitivePolynomial_nonnegative (grade + 3)))
    (fun grade => forwardComparisonPolynomial_zero L sigma gamma grade _ _ (errorPrimitivePolynomial_zero (grade + 1)))

theorem budgetForwardPolynomial_contract {L ell : ℝ} (parameters : PhaseParameters) (radius : ℝ)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) :
    ComparisonPolynomialContract (budgetForwardPolynomial parameters L radius) :=
  comparisonPolynomialContract_of_nonnegative_zero _
    (fun grade => forwardComparisonPolynomial_nonnegative admissible grade
      (linearBoundPolynomial_nonnegative (add_nonneg (ledgerConstantFour_nonnegative parameters L radius _)
        (ledgerConstantFive_nonnegative parameters L _)))
      (linearBoundPolynomial_nonnegative (mul_nonneg (by norm_num) (ledgerConstantFour_nonnegative parameters L radius _))))
    (fun grade => forwardComparisonPolynomial_zero L parameters.sigma0 parameters.gamma grade _ _ (by
      rw [linearBoundPolynomial_eval, mul_zero]))

/-- Package the actual canonical coefficients before entering the completed
operator interface. This keeps the concrete inverse proof witnesses out of
the operator-norm elaboration; every estimate is proved for this ledger. -/
theorem actualComparisonLedger (parameters : PhaseParameters) (L radius threshold : ℝ)
    (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold)
    (ell rho alpha delta parameter epsilon : ℝ)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius) (parameterSmall : |parameter| ≤ radius)
    (base : ACore parameters 3)
    (low : physicalBudget parameters base rho epsilon 10 < comparisonLowRadius parameters L radius threshold) :
    ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
      primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
      (∀ grade, ledgerSizeFour ledger grade ≤ ledgerConstantFour parameters L radius grade *
          physicalBudget parameters base rho epsilon (grade + 4) ∧
        ledgerSizeFive ledger grade ≤ ledgerConstantFive parameters L grade *
          physicalBudget parameters base rho epsilon (grade + 5)) ∧
      (∀ grade high, grade + 1 ≤ high → errorCoefficientSize ledger.val grade ≤
        (errorPrimitivePolynomial grade).eval
          (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)) ∧
      (∀ grade high, grade ≤ high → gaugeEpsilon (ledger.val.gaugeDeviation grade) ≤
        (gaugePrimitivePolynomial grade).eval
          (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)) ∧
      Nonempty (SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation) := by
  obtain ⟨frameSmall, seedSmall, margin, bounds, smooth⟩ := actualCanonicalComparisonData parameters L radius threshold
    radiusNonnegative thresholdPositive ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  exact ⟨physicalLedger parameters admissible rho alpha delta parameter epsilon base frameSmall seedSmall,
    margin, bounds,
    fun grade high ordered => physicalErrorSize_primitive parameters admissible rho alpha delta parameter epsilon base
      frameSmall seedSmall grade high ordered,
    fun grade high ordered => physicalGaugeSize_primitive parameters admissible rho alpha delta parameter epsilon base
      frameSmall grade high ordered,
    smooth⟩

/-- Full actual common-domain AO27–31/AP31–33 forward comparison.
All maps, the actual ledger, the compensated transfer, source range, and
both prescribed polynomial estimates are constructed on one original low
ball. No circular, compressed, boundary, or PDE inverse is a premise. -/
theorem actualForwardComparison (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualForwardComparisonGoal parameters L radius threshold := by
  have referenceAdmissible : Admissible L parameters.sigma0 parameters.gamma (min 1 L) :=
    ⟨positive, parameters.gamma_pos, parameters.gamma_lt_min, lt_min zero_lt_one positive, le_rfl⟩
  refine ⟨primitiveForwardPolynomial L parameters.sigma0 parameters.gamma,
    budgetForwardPolynomial parameters L radius, circularForwardConstant L parameters.sigma0 parameters.gamma,
    primitiveForwardPolynomial_contract referenceAdmissible,
    budgetForwardPolynomial_contract parameters radius referenceAdmissible,
    circularForwardConstant_nonnegative referenceAdmissible,
    comparisonLowRadius parameters L radius threshold,
    comparisonLowRadius_positive parameters L radius threshold positive thresholdPositive,
    comparisonLowRadius_le_one parameters L radius threshold, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low _bounded
  have supplied := actualComparisonLedger parameters L radius threshold
    radiusNonnegative thresholdPositive ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  let ledger := supplied.choose
  have margin := supplied.choose_spec.1
  have bounds := supplied.choose_spec.2.1
  have errorPrimitive := supplied.choose_spec.2.2.1
  have gaugePrimitive := supplied.choose_spec.2.2.2.1
  let smooth := Classical.choice supplied.choose_spec.2.2.2.2
  refine ⟨ledger, margin, actualComplementCancellation admissible, smooth,
    actualSmoothForwardComparison admissible ledger.val ledger.property.1 smooth, ?_⟩
  intro grade large
  refine ⟨actualCompletedForwardComparison admissible ledger.val ledger.property.1 smooth grade large,
    actualCompletedForwardComparison_circle_bound admissible ledger.val ledger.property.1 smooth grade large, ?_, ?_⟩
  · have bound := actualCompletedForwardComparison_difference_bound admissible ledger.val ledger.property.1 smooth grade large
    exact bound.trans (forwardComparisonPolynomial_bound admissible grade ledger.val
      (errorPrimitivePolynomial (grade + 1)) (gaugePrimitivePolynomial (grade + 3))
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base (grade + 3))
      (errorPrimitive (grade + 1) (grade + 3) (by omega))
      (gaugePrimitive (grade + 3) (grade + 3) le_rfl))
  · have errorBound := actualErrorSize_budget ledger (ledgerConstantFour parameters L radius) (ledgerConstantFive parameters L)
      (ledgerConstantFour_nonnegative parameters L radius) (ledgerConstantFive_nonnegative parameters L) bounds grade
    have gaugeBound := actualGaugeSize_budget ledger (ledgerConstantFour parameters L radius) (fun q => (bounds q).1) grade
    have bound := actualCompletedForwardComparison_difference_bound admissible ledger.val ledger.property.1 smooth grade large
    exact bound.trans (forwardComparisonPolynomial_bound admissible grade ledger.val
      (linearBoundPolynomial (ledgerConstantFour parameters L radius (grade + 1) + ledgerConstantFive parameters L (grade + 1)))
      (linearBoundPolynomial (4 * ledgerConstantFour parameters L radius (grade + 3)))
      (physicalBudget parameters base rho epsilon (grade + 7))
      (errorBound.trans_eq (linearBoundPolynomial_eval _ _).symm)
      (gaugeBound.trans_eq (linearBoundPolynomial_eval _ _).symm))

end Grad.GaugeCoefficients.Physical.Compensated
