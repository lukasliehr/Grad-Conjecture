import AKY13ActualLedgerReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- A single B8 neighborhood, chosen before scale/cells/field/grades, supplies
the actual uncompressed ER reduction. Only existing B6 ledger and determinant
inverse estimates are consumed. No inverse, projection law, B10-smallness,
cell truncation, or extra high-norm bound is assumed. -/
theorem actualOriginalB8CartesianReduction (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 8 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent := by
  obtain ⟨ledgerRadius, ledgerRadiusPositive, ledgerRadiusOne, gaugeConstants, higherConstants,
    gaugeConstantsNonnegative, _, supplied⟩ := actualLedger parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨min ledgerRadius (determinantLowRadius gaugeConstants),
    lt_min ledgerRadiusPositive (determinantLowRadius_positive gaugeConstants),
    (min_le_left _ _).trans ledgerRadiusOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  have lowSix := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 8)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans (min_le_right _ _)
  have unitSmall := ledgerSmall.trans ledgerRadiusOne
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitiveMargin, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      gaugeConstants grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall).actualCoherent
  have laws := fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon ledger.val.gaugeDeviation
    coherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall grade
  exact ⟨ledger, primitiveMargin, inverseCoherent, actualLedgerReduction_of_projection ledger inverseCoherent laws⟩

end Grad.CartesianUncompressed
