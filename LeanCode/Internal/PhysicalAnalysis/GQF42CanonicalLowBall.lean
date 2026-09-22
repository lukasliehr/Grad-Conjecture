import GQF41PrimitiveLedgerBounds
import GQF30CompletedComparison

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

def comparisonLowRadius (parameters : PhaseParameters) (L radius threshold : ℝ) : ℝ :=
  min (ledgerLowRadius parameters L radius threshold) (determinantLowRadius (ledgerConstantFour parameters L radius))

theorem comparisonLowRadius_positive (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (thresholdPositive : 0 < threshold) : 0 < comparisonLowRadius parameters L radius threshold :=
  lt_min (ledgerLowRadius_positive parameters positive radius thresholdPositive) (determinantLowRadius_positive _)

theorem comparisonLowRadius_le_one (parameters : PhaseParameters) (L radius threshold : ℝ) :
    comparisonLowRadius parameters L radius threshold ≤ 1 :=
  (min_le_left _ _).trans (ledgerLowRadius_le_one parameters L radius threshold)

theorem actualCanonicalComparisonData (parameters : PhaseParameters) (L radius threshold : ℝ)
    (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold)
    (ell rho alpha delta parameter epsilon : ℝ)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius) (parameterSmall : |parameter| ≤ radius)
    (base : ACore parameters 3)
    (low : physicalBudget parameters base rho epsilon 10 < comparisonLowRadius parameters L radius threshold) :
    ∃ (frameSmall : ‖frameInverseInput parameters admissible epsilon base 0‖ ≤ 1 / 4)
      (seedSmall : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4),
      primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
      (∀ grade,
        ledgerSizeFour (physicalLedger parameters admissible rho alpha delta parameter epsilon base frameSmall seedSmall) grade ≤
          ledgerConstantFour parameters L radius grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
        ledgerSizeFive (physicalLedger parameters admissible rho alpha delta parameter epsilon base frameSmall seedSmall) grade ≤
          ledgerConstantFive parameters L grade * physicalBudget parameters base rho epsilon (grade + 5)) ∧
      Nonempty (SmoothCompensatedCoreIsomorphism admissible
        (physicalLedgerData parameters admissible rho alpha delta parameter epsilon base).gaugeDeviation) := by
  have lowSix := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans (min_le_right _ _)
  have unitSmall := ledgerSmall.trans (ledgerLowRadius_le_one parameters L radius threshold)
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  have margins := actualInverseInput_margins parameters admissible radiusNonnegative thresholdPositive
    rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall
  let ledger := physicalLedger parameters admissible rho alpha delta parameter epsilon base margins.2.1 margins.2.2
  have lowFive : physicalBudget parameters base rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters base rho epsilon (by norm_num : 5 ≤ 6)).trans unitSmall
  have bounds := physicalLedger_bounds parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base margins.1 lowFive margins.2.1 margins.2.2
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      ledgerConstantFour parameters L radius grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (bounds grade).1
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    (ledgerConstantFour parameters L radius) (ledgerConstantFour_nonnegative parameters L radius) unitSmall gaugeBound determinantSmall).actualCoherent
  have laws := fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon ledger.val.gaugeDeviation
    coherent (ledgerConstantFour parameters L radius) (ledgerConstantFour_nonnegative parameters L radius) unitSmall gaugeBound determinantSmall grade
  have margin := determinant_base_margin parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    (ledgerConstantFour parameters L radius) (ledgerConstantFour_nonnegative parameters L radius) unitSmall gaugeBound determinantSmall
  exact ⟨margins.2.1, margins.2.2,
    (primitiveSize_low_margin parameters admissible radiusNonnegative thresholdPositive rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall).1,
    bounds, ⟨smoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation coherent inverseCoherent laws margin⟩⟩

end Grad.GaugeCoefficients.Physical.Compensated
