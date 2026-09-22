import AKBT23ActualB10NativeGaugeRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The accepted principal H1 realization on one B10 ball, with the
 same native gauge estimate retained for the actual rough field. -/
theorem actualOriginalB10NativeGaugeResolvent (parameters : PhaseParameters)
    (L radius primitiveThreshold operatorThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (operatorPositive : 0 < operatorThreshold)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ openUnitDisk) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧
              ∃ regular : FieldH1 →L[ℂ] FieldH1,
                (∀ field, valueInclusion (regular field) = startupGenuinePrincipalL2 scalar smooth compact
                  admissible ledger.val ledger.property.1 inverseCoherent (valueInclusion field)) ∧
                ‖startupGenuinePrincipalL2 scalar smooth compact admissible ledger.val ledger.property.1 inverseCoherent‖ < operatorThreshold ∧
                ‖regular‖ < operatorThreshold ∧
                ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
                  physicalBudget parameters base rho epsilon 6 ≤ 1 ∧
                  (∀ grade, ‖ledger.val.gaugeDeviation grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4)) ∧
                  physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants := by
  let payment := 4 * startupCutoffConstant scalar smooth compact * 3 *
    startupPrincipalFixedConstant * startupEREmbeddingConstant
  have paymentPositive : 0 < payment := by
    have := startupCutoffConstant_positive scalar smooth compact
    have := startupPrincipalFixedConstant_positive
    have := startupEREmbeddingConstant_positive
    dsimp [payment]
    positivity
  have denominatorPositive : 0 < payment + 1 := by positivity
  have paid : 4 * (startupCutoffConstant scalar smooth compact *
      (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * (operatorThreshold / (payment + 1))))) <
        operatorThreshold := by
    have rearrange : 4 * (startupCutoffConstant scalar smooth compact *
        (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * (operatorThreshold / (payment + 1))))) =
        payment * operatorThreshold / (payment + 1) := by dsimp [payment]; ring
    rw [rearrange]
    exact (div_lt_iff₀ denominatorPositive).mpr (by nlinarith)
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ := actualOriginalB10NativeGaugeRows parameters L radius primitiveThreshold
    (operatorThreshold / (payment + 1)) positive radiusNonnegative primitivePositive
    (div_pos operatorPositive denominatorPositive)
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨ledger, primitiveMargin, inverseCoherent, reduction, small, gauge⟩ := supplied
    ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨regular, same, coarseBound, fineBound⟩ := startupGenuinePrincipalH1_exists scalar smooth compact included
    ledger inverseCoherent (operatorThreshold / (payment + 1)) small
  exact ⟨ledger, primitiveMargin, inverseCoherent, reduction,
    regular, same, coarseBound.trans_lt paid, fineBound.trans_lt paid,gauge⟩

end Grad.CartesianStartup
