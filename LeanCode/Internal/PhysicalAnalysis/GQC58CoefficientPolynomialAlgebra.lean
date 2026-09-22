import GQC57PolynomialCalculus

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem constantPolynomial_bound {Value : Type*} [SeminormedAddCommGroup Value]
    (field : Value) {constant : ℝ} (bound : ‖field‖ ≤ constant) (value : ℝ) :
    ‖field‖ ≤ (Polynomial.C constant).eval value := bound.trans_eq (Polynomial.eval_C).symm

def productPolynomial (grade : ℕ) (outer inner : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (gradeProductConstant grade) * outer * inner

theorem productPolynomial_nonnegative (grade : ℕ) {outer inner : Polynomial ℝ}
    (outerPositive : NonnegativeCoefficients outer) (innerPositive : NonnegativeCoefficients inner) :
    NonnegativeCoefficients (productPolynomial grade outer inner) :=
  ((nonnegativeCoefficients_const _ (gradeProductConstant_nonnegative grade)).mul outerPositive).mul innerPositive

theorem productPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input middle output : ℕ} (outer : Coefficient L sigma gamma ell grade middle output)
    (inner : Coefficient L sigma gamma ell grade input middle) {outerP innerP : Polynomial ℝ} {value : ℝ}
    (outerBound : ‖outer‖ ≤ outerP.eval value) (innerBound : ‖inner‖ ≤ innerP.eval value) :
    ‖coefficientComposition admissible grade outer inner‖ ≤ (productPolynomial grade outerP innerP).eval value := by
  have bound := (coefficientComposition_norm_le admissible grade outer inner).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left outerBound (gradeProductConstant_nonnegative grade)) innerBound
      (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade) ((norm_nonneg _).trans outerBound)))
  exact bound.trans_eq (by simp only [productPolynomial, Polynomial.eval_mul, Polynomial.eval_C])

theorem polynomial_add_norm_bound {Value : Type*} [SeminormedAddCommGroup Value]
    (first second : Value) {firstP secondP : Polynomial ℝ} {value : ℝ}
    (firstBound : ‖first‖ ≤ firstP.eval value) (secondBound : ‖second‖ ≤ secondP.eval value) :
    ‖first + second‖ ≤ (firstP + secondP).eval value :=
  ((norm_add_le first second).trans (add_le_add firstBound secondBound)).trans_eq (Polynomial.eval_add).symm

theorem polynomial_sub_norm_bound {Value : Type*} [SeminormedAddCommGroup Value]
    (first second : Value) {firstP secondP : Polynomial ℝ} {value : ℝ}
    (firstBound : ‖first‖ ≤ firstP.eval value) (secondBound : ‖second‖ ≤ secondP.eval value) :
    ‖first - second‖ ≤ (firstP + secondP).eval value :=
  ((norm_sub_le first second).trans (add_le_add firstBound secondBound)).trans_eq (Polynomial.eval_add).symm

def identityNormPolynomial (grade : ℕ) : Polynomial ℝ := Polynomial.C (Fintype.card (DerivativeIndex grade) : ℝ)

theorem identityNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (identityNormPolynomial grade) :=
  nonnegativeCoefficients_const _ (Nat.cast_nonneg _)

theorem identityNormPolynomial_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ) (value : ℝ) :
    ‖identityFamily L sigma gamma ell dimension grade‖ ≤ (identityNormPolynomial grade).eval value :=
  (identityFamily_norm_le L sigma gamma ell dimension grade).trans_eq (Polynomial.eval_C).symm

def linearBoundPolynomial (constant : ℝ) : Polynomial ℝ := Polynomial.C constant * Polynomial.X

theorem linearBoundPolynomial_nonnegative {constant : ℝ} (nonnegative : 0 ≤ constant) :
    NonnegativeCoefficients (linearBoundPolynomial constant) :=
  (nonnegativeCoefficients_const _ nonnegative).mul nonnegativeCoefficients_X

theorem linearBoundPolynomial_eval (constant value : ℝ) :
    (linearBoundPolynomial constant).eval value = constant * value := by
  simp only [linearBoundPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem linearBoundPolynomial_bound {Value : Type*} [SeminormedAddCommGroup Value]
    (field : Value) {constant value : ℝ} (bound : ‖field‖ ≤ constant * value) :
    ‖field‖ ≤ (linearBoundPolynomial constant).eval value := bound.trans_eq (linearBoundPolynomial_eval constant value).symm

end Grad.GaugeCoefficients.Physical.Compensated
