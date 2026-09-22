import AKU12SameWidthAxisMultiplierEnvelope
import PA7EnvelopeConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds

/-- A finite natural power needs only one high factor. -/
theorem nonnegative_add_power_one_high (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (grade : ℕ) :
    (first + second)^grade ≤ 2^grade * (first^grade + second^grade) := by
  have step : first + second ≤ 2 * max first second := by
    linarith [le_max_left first second,le_max_right first second]
  apply (pow_le_pow_left₀ (add_nonneg firstNonnegative secondNonnegative) step grade).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) grade)
  rcases le_total first second with ordered | ordered
  · rw [max_eq_right ordered]
    exact le_add_of_nonneg_left (pow_nonneg firstNonnegative grade)
  · rw [max_eq_left ordered]
    exact le_add_of_nonneg_right (pow_nonneg secondNonnegative grade)

/-- The literal original axis weight admits the one-high cell split. This
keeps sigma unchanged and spends no extra Cartesian or circle derivatives. -/
theorem originalAxisWeight_one_high (parameters : PhaseParameters) (grade : ℕ) (shift base : ℤ) :
    Grad.AxisCore.axisWeight parameters grade (shift + base) ≤
      2 ^ grade * (tameWeight parameters grade shift * Grad.AxisCore.axisWeight parameters 0 base +
        tameWeight parameters 0 shift * Grad.AxisCore.axisWeight parameters grade base) := by
  have frequency : cellFrequency (shift+base) ≤ cellPolynomialWeight shift + cellFrequency base :=
    (cellFrequency_add_le shift base).trans
      (add_le_add (Grad.Constraints.Multipliers.frequency_le_polynomial shift) le_rfl)
  have exponential : Real.exp (parameters.sigma0 * cellFrequency (shift+base)) ≤
      Real.exp (parameters.sigma0 * cellFrequency shift) *
        Real.exp (parameters.sigma0 * cellFrequency base) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [cellFrequency_add_le shift base,parameters.sigma0_pos]
  have power : cellFrequency (shift+base)^grade ≤
      2^grade * (cellPolynomialWeight shift ^ grade + cellFrequency base ^ grade) :=
    (pow_le_pow_left₀ (cellFrequency_pos _).le frequency grade).trans
      (nonnegative_add_power_one_high _ _ (cellPolynomialWeight_pos shift).le (cellFrequency_pos base).le grade)
  change Real.exp (parameters.sigma0 * cellFrequency (shift+base)) * cellFrequency (shift+base)^grade ≤ _
  apply (mul_le_mul exponential power (pow_nonneg (cellFrequency_pos _).le grade)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq
  simp only [tameWeight,Grad.AxisCore.axisWeight,pow_zero,mul_one]
  ring

end Grad.FinitePhysicalJetLift
