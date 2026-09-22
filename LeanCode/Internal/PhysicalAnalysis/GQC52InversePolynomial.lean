import GQC48GaugeActionBounds
import Mathlib.Algebra.Polynomial.Basic

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.GaugeCoefficients.Physical.InverseAllocation

def NonnegativeCoefficients (polynomial : Polynomial ℝ) : Prop := ∀ order, 0 ≤ polynomial.coeff order

theorem NonnegativeCoefficients.add {first second : Polynomial ℝ}
    (firstNonnegative : NonnegativeCoefficients first) (secondNonnegative : NonnegativeCoefficients second) :
    NonnegativeCoefficients (first + second) := by
  intro order
  rw [Polynomial.coeff_add]
  exact add_nonneg (firstNonnegative order) (secondNonnegative order)

theorem NonnegativeCoefficients.mul {first second : Polynomial ℝ}
    (firstNonnegative : NonnegativeCoefficients first) (secondNonnegative : NonnegativeCoefficients second) :
    NonnegativeCoefficients (first * second) := by
  intro order
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun index _ => mul_nonneg (firstNonnegative index.1) (secondNonnegative index.2))

theorem nonnegativeCoefficients_const (value : ℝ) (nonnegative : 0 ≤ value) :
    NonnegativeCoefficients (Polynomial.C value) := by
  intro order
  simp only [Polynomial.coeff_C]
  split <;> positivity

theorem nonnegativeCoefficients_X : NonnegativeCoefficients (Polynomial.X : Polynomial ℝ) := by
  intro order
  simp only [Polynomial.coeff_X]
  split <;> positivity

/-- Finite same-grade reciprocal derivative polynomial on the SAME base
margin 1/2. The recursion only allocates actual coefficient slots. -/
def inverseSlotPolynomial (grade order : ℕ) : Polynomial ℝ :=
  Nat.rec 0 (fun _ previous =>
    Polynomial.C (2 * splitCeiling grade) * Polynomial.X * (Polynomial.C 1 + previous) + previous) order

theorem inverseSlotPolynomial_zero (grade : ℕ) : inverseSlotPolynomial grade 0 = 0 := rfl

theorem inverseSlotPolynomial_succ (grade order : ℕ) :
    inverseSlotPolynomial grade (order + 1) =
      Polynomial.C (2 * splitCeiling grade) * Polynomial.X *
        (Polynomial.C 1 + inverseSlotPolynomial grade order) + inverseSlotPolynomial grade order := rfl

theorem inverseSlotPolynomial_nonnegative (grade order : ℕ) :
    NonnegativeCoefficients (inverseSlotPolynomial grade order) := by
  induction order with
  | zero => intro index; simp [inverseSlotPolynomial_zero]
  | succ order ih =>
    rw [inverseSlotPolynomial_succ]
    exact (((nonnegativeCoefficients_const _ (mul_nonneg (by norm_num) (splitCeiling_nonnegative grade))).mul
      nonnegativeCoefficients_X).mul ((nonnegativeCoefficients_const 1 (by norm_num)).add ih)).add ih

theorem inverseSlotPolynomial_eval_succ (grade order : ℕ) (value : ℝ) :
    (inverseSlotPolynomial grade (order + 1)).eval value =
      2 * splitCeiling grade * value * (1 + (inverseSlotPolynomial grade order).eval value) +
        (inverseSlotPolynomial grade order).eval value := by
  simp only [inverseSlotPolynomial_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem inverseSlotPolynomial_eval_zero (grade order : ℕ) : (inverseSlotPolynomial grade order).eval 0 = 0 := by
  induction order with
  | zero => simp [inverseSlotPolynomial_zero]
  | succ order ih => rw [inverseSlotPolynomial_eval_succ, ih]; ring

theorem inverseSlotPolynomial_eval_nonnegative (grade order : ℕ) {value : ℝ} (nonnegative : 0 ≤ value) :
    0 ≤ (inverseSlotPolynomial grade order).eval value := by
  induction order with
  | zero => simp [inverseSlotPolynomial_zero]
  | succ order ih =>
    rw [inverseSlotPolynomial_eval_succ]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (splitCeiling_nonnegative grade)) nonnegative)
      (add_nonneg zero_le_one ih)) ih

theorem inverseSlotPolynomial_eval_monotone_order (grade : ℕ) {value : ℝ} (nonnegative : 0 ≤ value) :
    Monotone (fun order => (inverseSlotPolynomial grade order).eval value) := by
  apply monotone_nat_of_le_succ
  intro order
  rw [inverseSlotPolynomial_eval_succ]
  exact le_add_of_nonneg_left (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (splitCeiling_nonnegative grade)) nonnegative)
    (add_nonneg zero_le_one (inverseSlotPolynomial_eval_nonnegative grade order nonnegative)))

end Grad.GaugeCoefficients.Physical.Compensated
