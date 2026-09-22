import GC17Interface

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame

theorem primitiveSize_bound {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3) (grade : ℕ) :
    primitiveSize parameters admissible rho alpha delta parameter epsilon field grade ≤
      actualFrameConstant parameters L radius grade *
        physicalBudget parameters field rho epsilon (grade + 4) :=
  actualFrameCoefficients_norm_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall (GradeCore.ofCoreLinear (grade := grade + 4) field)

/-- One fixed B6 radius, retaining the externally prescribed AP27 threshold
and simultaneously furnishing both actual base inverses. -/
def ledgerLowRadius (parameters : PhaseParameters) (L radius threshold : ℝ) : ℝ :=
  min 1 (min (threshold / (actualFrameConstant parameters L radius 2 + 1))
    (4 * (actualFrameConstant parameters L radius 0 + 1))⁻¹)

theorem ledgerLowRadius_positive (parameters : PhaseParameters) {L threshold : ℝ}
    (positive : 0 < L) (radius : ℝ) (thresholdPositive : 0 < threshold) :
    0 < ledgerLowRadius parameters L radius threshold := by
  have zeroConstant := actualFrameConstant_nonnegative parameters positive radius 0
  have twoConstant := actualFrameConstant_nonnegative parameters positive radius 2
  unfold ledgerLowRadius
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem ledgerLowRadius_le_one (parameters : PhaseParameters) (L radius threshold : ℝ) :
    ledgerLowRadius parameters L radius threshold ≤ 1 := min_le_left _ _

theorem primitiveSize_low_margin {L ell radius threshold : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold)
    (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ ledgerLowRadius parameters L radius threshold) :
    primitiveSize parameters admissible rho alpha delta parameter epsilon field 2 ≤ threshold ∧
      primitiveSize parameters admissible rho alpha delta parameter epsilon field 0 ≤ 1 / 4 := by
  have zeroConstant := actualFrameConstant_nonnegative parameters admissible.1 radius 0
  have twoConstant := actualFrameConstant_nonnegative parameters admissible.1 radius 2
  have thresholdLow : physicalBudget parameters field rho epsilon 6 ≤
      threshold / (actualFrameConstant parameters L radius 2 + 1) :=
    low.trans ((min_le_right _ _).trans (min_le_left _ _))
  have baseLow : physicalBudget parameters field rho epsilon 4 ≤
      (4 * (actualFrameConstant parameters L radius 0 + 1))⁻¹ :=
    (physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 6)).trans
      (low.trans ((min_le_right _ _).trans (min_le_right _ _)))
  constructor
  · apply (primitiveSize_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field 2).trans
    apply (mul_le_mul_of_nonneg_left thresholdLow twoConstant).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < actualFrameConstant parameters L radius 2 + 1)).mpr
    nlinarith
  · apply (primitiveSize_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field 0).trans
    apply (mul_le_mul_of_nonneg_left baseLow zeroConstant).trans
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (actualFrameConstant parameters L radius 0 + 1))).mpr
    linarith

end Grad.GaugeCoefficients.Physical.Ledger
