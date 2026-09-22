import ASX26ActualExceptionalConsumer
import ACB20NativeCenterConsumer

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.ActualCenterVolterra Grad.ActualExceptionalInverse Grad.CircularHighWeak
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

theorem ordinaryDilation_derivative_bound {rank : ℕ} {scale : ℝ}
    (positive : 0 < scale) (bounded : scale ≤ 1) (field : ClosedJet 1)
    (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative (dilationJet scale field) rank word)‖ ≤
      scale⁻¹ * ‖closedContinuousToDiskL2 (closedDerivative field rank word)‖ := by
  have identity : closedDerivative (dilationJet scale field) rank word =
      scale ^ rank • (closedDerivative field rank word).comp (dilationClosedMap scale positive.le bounded) := by
    apply ContinuousMap.ext
    intro point
    exact dilationJet_derivative positive.le bounded field word point
  rw [identity, closedValueL2_real_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg positive.le _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ positive.le bounded)).trans
    (closedValueL2_dilation_bound positive bounded _)

theorem ordinaryPower_family_bound {rank : ℕ} (power : ℕ) (field : ClosedJet 1)
    (word : CartesianWord rank) {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) :
    ‖closedContinuousToDiskL2 (originalPowerDerivativeFamily 0 0 1 0 (power + 1) field word scale)‖ ≤
      ‖closedContinuousToDiskL2 (closedDerivative field rank word)‖ := by
  rw [originalPowerDerivativeFamily, unweightedJet, closedValueL2_real_smul, norm_smul]
  by_cases zeroScale : scale = 0
  · simp only [zeroScale, zero_pow (by omega : power + 1 ≠ 0), norm_zero, zero_mul]
    exact norm_nonneg _
  · have positive : 0 < scale := lt_of_le_of_ne nonnegative (Ne.symm zeroScale)
    rw [Real.norm_of_nonneg (pow_nonneg nonnegative _)]
    apply (mul_le_mul_of_nonneg_left (ordinaryDilation_derivative_bound positive bounded field word)
      (pow_nonneg nonnegative (power + 1))).trans
    rw [← mul_assoc, pow_succ, mul_assoc (scale ^ power), mul_inv_cancel₀ zeroScale, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ nonnegative bounded)

/-- The literal compact Euler integral is bounded at the same ordinary grade.
No weighted admissibility is asserted at zero phase. -/
theorem ordinaryPower_derivative_bound {rank : ℕ} (power : ℕ) (field : ClosedJet 1)
    (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative (powerDilationJet (power + 1) field) rank word)‖ ≤
      ‖closedContinuousToDiskL2 (closedDerivative field rank word)‖ := by
  have continuousFamily := originalPowerDerivativeFamily_continuous 0 0 1 0 (power + 1) field word
  have imageContinuous := (closedValueL2Continuous 1).continuous.comp continuousFamily
  have identity := originalPower_weighted_derivative_map 0 0 1 0 (power + 1) field word
  rw [unweightedJet] at identity
  rw [identity, closedValueL2_integral continuousFamily.continuousOn.integrableOn_Icc]
  calc
    _ ≤ ∫ scale in Icc (0 : ℝ) 1,
        ‖closedContinuousToDiskL2 (originalPowerDerivativeFamily 0 0 1 0 (power + 1) field word scale)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _scale in Icc (0 : ℝ) 1,
        ‖closedContinuousToDiskL2 (closedDerivative field rank word)‖ := by
      apply integral_mono_ae imageContinuous.norm.continuousOn.integrableOn_Icc
        continuous_const.continuousOn.integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with scale scaleIn
      exact ordinaryPower_family_bound power field word scaleIn.1 scaleIn.2
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_const]
      simp

def ordinaryPowerConstant (grade : ℕ) : ℝ := Real.sqrt (Fintype.card (DerivativeIndex grade))

theorem ordinaryPowerConstant_nonnegative (grade : ℕ) : 0 ≤ ordinaryPowerConstant grade := Real.sqrt_nonneg _

theorem ordinaryPower_row_bound (grade power : ℕ) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (powerDilationJet (power + 1) field)‖ ≤
      ordinaryPowerConstant grade * ‖unitSobolevRow grade field‖ := by
  apply apRow_norm_bound_of_coordinates _ _ (norm_nonneg _)
  intro index
  rw [unitSobolevRow_coordinate]
  exact (ordinaryPower_derivative_bound power field (apIndexWord index)).trans
    (unitSobolev_derivative_bound grade field index)

theorem ordinaryPower_native_bound (grade power : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (powerDilationJet (power + 1) field)‖ ≤
      ordinaryPowerConstant grade * ‖unitDiskCoreInto grade field‖ := by
  simpa only [unitDiskCore_norm] using ordinaryPower_row_bound grade power field

end Grad.ExceptionalNative
