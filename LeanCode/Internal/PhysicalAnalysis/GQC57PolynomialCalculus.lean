import GQC56RadialCoefficientBounds

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Neumann.Regularity

theorem NonnegativeCoefficients.eval_nonnegative {polynomial : Polynomial ℝ}
    (positive : NonnegativeCoefficients polynomial) {value : ℝ} (nonnegative : 0 ≤ value) :
    0 ≤ polynomial.eval value := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  exact Finset.sum_nonneg (fun index _ => mul_nonneg (positive index) (pow_nonneg nonnegative index))

theorem NonnegativeCoefficients.eval_monotone {polynomial : Polynomial ℝ}
    (positive : NonnegativeCoefficients polynomial) {first second : ℝ}
    (nonnegative : 0 ≤ first) (ordered : first ≤ second) : polynomial.eval first ≤ polynomial.eval second := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum]
  exact Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonnegative ordered index) (positive index))

def substitutedInversePolynomial (grade order : ℕ) (input : Polynomial ℝ) : Polynomial ℝ :=
  Nat.rec 0 (fun _ previous =>
    Polynomial.C (2 * splitCeiling grade) * input * (Polynomial.C 1 + previous) + previous) order

theorem substitutedInversePolynomial_nonnegative (grade order : ℕ) {input : Polynomial ℝ}
    (positive : NonnegativeCoefficients input) : NonnegativeCoefficients (substitutedInversePolynomial grade order input) := by
  induction order with
  | zero => intro index; simp [substitutedInversePolynomial]
  | succ order ih =>
    exact (((nonnegativeCoefficients_const _ (mul_nonneg (by norm_num) (splitCeiling_nonnegative grade))).mul positive).mul
      ((nonnegativeCoefficients_const 1 zero_le_one).add ih)).add ih

theorem substitutedInversePolynomial_eval (grade order : ℕ) (input : Polynomial ℝ) (value : ℝ) :
    (substitutedInversePolynomial grade order input).eval value =
      (inverseSlotPolynomial grade order).eval (input.eval value) := by
  induction order with
  | zero => simp [substitutedInversePolynomial, inverseSlotPolynomial_zero]
  | succ order ih =>
    change (Polynomial.C _ * input * (Polynomial.C 1 + substitutedInversePolynomial grade order input) +
      substitutedInversePolynomial grade order input).eval value = _
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_C, ih, inverseSlotPolynomial_eval_succ]

def inverseNormPolynomial (grade : ℕ) (input : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (Fintype.card (DerivativeIndex grade) : ℝ) *
    (Polynomial.C 1 + substitutedInversePolynomial grade (grade + 1) input)

theorem inverseNormPolynomial_nonnegative (grade : ℕ) {input : Polynomial ℝ}
    (positive : NonnegativeCoefficients input) : NonnegativeCoefficients (inverseNormPolynomial grade input) :=
  (nonnegativeCoefficients_const _ (Nat.cast_nonneg _)).mul
    ((nonnegativeCoefficients_const 1 zero_le_one).add (substitutedInversePolynomial_nonnegative grade (grade + 1) positive))

theorem inverseNormPolynomial_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension) (coherent : FamilyCoherent coefficient)
    (small : ‖coefficient 0‖ ≤ 1 / 2) (grade : ℕ) (input : Polynomial ℝ) (value : ℝ)
    (inputBound : ‖coefficient grade‖ ≤ input.eval value) :
    ‖inverseFamily admissible coefficient grade‖ ≤ (inverseNormPolynomial grade input).eval value := by
  have deviation := (inverse_deviation_polynomial_bound admissible positive coefficient coherent small grade).trans
    (mul_le_mul_of_nonneg_left ((inverseSlotPolynomial_nonnegative grade (grade + 1)).eval_monotone
      (norm_nonneg _) inputBound) (Nat.cast_nonneg _))
  have identity := Grad.GaugeCoefficients.Physical.Ledger.identityFamily_norm_le L sigma gamma ell dimension grade
  have bound := (norm_le_norm_sub_add (inverseFamily admissible coefficient grade)
    (gradedIdentityCoefficient L sigma gamma ell grade dimension)).trans (add_le_add deviation identity)
  apply bound.trans_eq
  simp only [inverseNormPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    substitutedInversePolynomial_eval]
  ring

end Grad.GaugeCoefficients.Physical.Compensated
