import GC17PhysicalWitness

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

def ledgerConstantFour (parameters : PhaseParameters) (L radius : ℝ) (grade : ℕ) : ℝ :=
  |(transposeProfile 4 3 3 (inverseFrameProfile parameters L)).deviation grade| +
    |(inverseSeedProfile parameters.sigma0 radius).deviation grade| +
    |(gaugeProfile (seedMatrixProfile parameters.sigma0 radius) (seedDerivativeProfile parameters.sigma0 radius)
      (inverseFrameProfile parameters L)).deviation grade| +
    |(fluxProfile (frameProfile parameters L) (inverseFrameProfile parameters L)).deviation grade| +
    |(traceProfile (inverseSeedProfile parameters.sigma0 radius) (inverseFrameProfile parameters L)).deviation grade|

def ledgerConstantFive (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  |(rotatedFrameProfile parameters L).deviation grade| +
    |(rotatedProductProfile planarFrameColumns (rotatedFrameProfile parameters L)
      (inverseFrameProfile parameters L)).deviation grade| +
    |(rotatedProductProfile thirdFrameColumn (rotatedFrameProfile parameters L)
      (inverseFrameProfile parameters L)).deviation grade|

theorem ledgerConstantFour_nonnegative (parameters : PhaseParameters) (L radius : ℝ) (grade : ℕ) :
    0 ≤ ledgerConstantFour parameters L radius grade := by
  unfold ledgerConstantFour
  positivity

theorem ledgerConstantFive_nonnegative (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 ≤ ledgerConstantFive parameters L grade := by
  unfold ledgerConstantFive
  positivity

theorem FamilyEstimate.absoluteBound {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) (grade : ℕ) :
    ‖actual grade - reference grade‖ ≤
      |profile.deviation grade| * physicalBudget parameters field rho epsilon (grade + offset) := by
  have bound := (estimate.deviationBound grade).trans
    (mul_le_mul_of_nonneg_right (le_abs_self (profile.deviation grade))
      (physicalBudget_nonnegative parameters field rho epsilon (offset + grade)))
  simpa only [Nat.add_comm] using bound

theorem physicalLedger_bounds {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3)
    (lowFour : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (lowFive : physicalBudget parameters field rho epsilon 5 ≤ 1)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4) (grade : ℕ) :
    ledgerSizeFour (physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase) grade ≤
      ledgerConstantFour parameters L radius grade * physicalBudget parameters field rho epsilon (grade + 4) ∧
    ledgerSizeFive (physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase) grade ≤
      ledgerConstantFive parameters L grade * physicalBudget parameters field rho epsilon (grade + 5) := by
  have frameEstimate := fullFrameFamily_estimate parameters admissible rho epsilon epsilonSmall field
  have inverseEstimate := actualFrameInverse_estimate parameters admissible rho epsilon epsilonSmall field lowFour frameBase
  have seedEstimate := seedMatrixFamily_estimate parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall field
  have seedInverseEstimate := actualSeedInverse_estimate parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall field lowFour seedBase
  have derivativeEstimate := seedDerivativeFamily_estimate parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall field
  have rotatedEstimate := actualRotatedFrame_estimate parameters admissible rho epsilon epsilonSmall field
  have transposeBound := (transposeFamily_estimate admissible lowFour inverseEstimate).absoluteBound grade
  have seedBound := seedInverseEstimate.absoluteBound grade
  have gaugeBound := (gaugeFamily_estimate admissible lowFour seedEstimate derivativeEstimate inverseEstimate).absoluteBound grade
  have fluxBound := (fluxFamily_estimate admissible lowFour frameEstimate inverseEstimate).absoluteBound grade
  have traceBound := (traceFamily_estimate admissible lowFour seedInverseEstimate inverseEstimate).absoluteBound grade
  have rotatedBound := rotatedEstimate.absoluteBound grade
  change ‖actualRotatedFrame parameters admissible epsilon field grade - 0‖ ≤ _ at rotatedBound
  rw [sub_zero] at rotatedBound
  have inverseFive := inverseEstimate.offset_mono (by norm_num : 4 ≤ 5)
  have planarBound := (rotatedProductFamily_estimate admissible lowFive planarFrameColumns rotatedEstimate inverseFive).absoluteBound grade
  have thirdBound := (rotatedProductFamily_estimate admissible lowFive thirdFrameColumn rotatedEstimate inverseFive).absoluteBound grade
  constructor
  · exact (add_le_add (add_le_add (add_le_add (add_le_add transposeBound seedBound) gaugeBound) fluxBound) traceBound).trans_eq (by
      unfold ledgerConstantFour
      ring)
  · exact (add_le_add (add_le_add rotatedBound planarBound) thirdBound).trans_eq (by
      unfold ledgerConstantFive
      ring)

end Grad.GaugeCoefficients.Physical.Ledger
