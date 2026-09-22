import AKAS11LocalizedPrincipalResolvent

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

/-- One original B10 ball, selected before ell and the unknown, makes the
 actual full localized ER11 principal resolvent small on BOTH L2 and H1.
 Literal a,c,s, angular mean subtraction, inverse covectors, curl signs
 and all fixed tensor multiplicities are retained. -/
theorem actualOriginalB10PrincipalResolventSmall (parameters : PhaseParameters)
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
              ActualStartupKernelRealization ledger inverseCoherent ∧
              ∃ regular : FieldH1 →L[ℂ] FieldH1,
                (∀ field, valueInclusion (regular field) = startupActualPrincipalL2 scalar smooth compact
                  admissible ledger.val ledger.property.1 inverseCoherent (valueInclusion field)) ∧
                ‖startupActualPrincipalL2 scalar smooth compact admissible ledger.val ledger.property.1 inverseCoherent‖ < operatorThreshold ∧
                ‖regular‖ < operatorThreshold := by
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
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ := actualOriginalB10SmallRows parameters L radius primitiveThreshold
    (operatorThreshold / (payment + 1)) positive radiusNonnegative primitivePositive
    (div_pos operatorPositive denominatorPositive)
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨ledger, primitiveMargin, inverseCoherent, reduction, realization, small⟩ := supplied
    ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨regular, same, coarseBound, fineBound⟩ := startupActualPrincipalH1_exists scalar smooth compact included
    ledger inverseCoherent (operatorThreshold / (payment + 1)) small
  exact ⟨ledger, primitiveMargin, inverseCoherent, reduction, realization,
    regular, same, coarseBound.trans_lt paid, fineBound.trans_lt paid⟩

end Grad.CartesianStartup
