import GC14FrameBound
import GC12Powers
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

theorem seedProductConstant_nonnegative (grade : ℕ) : 0 ≤ gradeProductConstant grade := by
  unfold gradeProductConstant
  positivity

/-- The elementary entire-series estimate used for the prescribed finite
harmonic seed. Its product is the already proved original-width product. -/
theorem seedCoefficientPower_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) (power : ℕ) :
    ‖gradedCoefficientPower admissible coefficient power‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        (gradeProductConstant grade * ‖coefficient‖) ^ power := by
  induction power with
  | zero => simp only [gradedCoefficientPower_zero, pow_zero, mul_one, le_refl]
  | succ power inductionHypothesis =>
    rw [gradedCoefficientPower_succ]
    calc
      _ ≤ gradeProductConstant grade * ‖coefficient‖ *
          ‖gradedCoefficientPower admissible coefficient power‖ :=
        coefficientComposition_norm_le admissible grade _ _
      _ ≤ gradeProductConstant grade * ‖coefficient‖ *
          (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
            (gradeProductConstant grade * ‖coefficient‖) ^ power) :=
        mul_le_mul_of_nonneg_left inductionHypothesis
          (mul_nonneg (seedProductConstant_nonnegative grade) (norm_nonneg coefficient))
      _ = _ := by rw [pow_succ]; ring

def seedExponentialTerm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) (power : ℕ) :
    Coefficient L sigma gamma ell grade dimension dimension :=
  ((power.factorial : ℂ)⁻¹) • gradedCoefficientPower admissible coefficient power

theorem seedExponentialTerm_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) (power : ℕ) :
    ‖seedExponentialTerm admissible coefficient power‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        ((gradeProductConstant grade * ‖coefficient‖) ^ power / power.factorial) := by
  have factorialNorm : ‖(power.factorial : ℂ)⁻¹‖ = (power.factorial : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  unfold seedExponentialTerm
  calc
    _ ≤ ‖(power.factorial : ℂ)⁻¹‖ * ‖gradedCoefficientPower admissible coefficient power‖ :=
      coefficientScalarNorm_le _ _
    _ = (power.factorial : ℝ)⁻¹ * ‖gradedCoefficientPower admissible coefficient power‖ := by
      rw [factorialNorm]
    _ ≤ (power.factorial : ℝ)⁻¹ *
        (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
          (gradeProductConstant grade * ‖coefficient‖) ^ power) :=
      mul_le_mul_of_nonneg_left (seedCoefficientPower_norm_le admissible coefficient power)
        (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem seedExponentialTerm_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    Summable (fun power : ℕ => ‖seedExponentialTerm admissible coefficient power‖) := by
  apply Summable.of_nonneg_of_le (fun power => norm_nonneg
    (seedExponentialTerm admissible coefficient power))
    (seedExponentialTerm_norm_le admissible coefficient)
  exact (NormedSpace.expSeries_div_hasSum_exp
    (gradeProductConstant grade * ‖coefficient‖)).summable.mul_left _

def seedCoefficientExponential {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    Coefficient L sigma gamma ell grade dimension dimension :=
  ∑' power : ℕ, seedExponentialTerm admissible coefficient power

theorem seedCoefficientExponential_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    ‖seedCoefficientExponential admissible coefficient‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        Real.exp (gradeProductConstant grade * ‖coefficient‖) := by
  have exponential := NormedSpace.expSeries_div_hasSum_exp
    (gradeProductConstant grade * ‖coefficient‖)
  unfold seedCoefficientExponential
  calc
    _ ≤ ∑' power : ℕ, ‖seedExponentialTerm admissible coefficient power‖ :=
      norm_tsum_le_tsum_norm (seedExponentialTerm_norm_summable admissible coefficient)
    _ ≤ ∑' power : ℕ, ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        ((gradeProductConstant grade * ‖coefficient‖) ^ power / power.factorial) :=
      (seedExponentialTerm_norm_summable admissible coefficient).tsum_le_tsum
        (seedExponentialTerm_norm_le admissible coefficient) (exponential.summable.mul_left _)
    _ = _ := by
      rw [exponential.summable.tsum_mul_left, exponential.tsum_eq, Real.exp_eq_exp_ℝ]

end Grad.GaugeCoefficients.Physical.Frame
