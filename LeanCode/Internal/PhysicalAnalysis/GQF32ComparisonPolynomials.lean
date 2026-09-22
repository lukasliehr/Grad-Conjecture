import GQF31LedgerSizeBounds

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem NonnegativeCoefficients.pow {polynomial : Polynomial ℝ}
    (nonnegative : NonnegativeCoefficients polynomial) (order : ℕ) : NonnegativeCoefficients (polynomial ^ order) := by
  induction order with
  | zero => simpa using nonnegativeCoefficients_const 1 zero_le_one
  | succ order ih => simpa only [pow_succ] using ih.mul nonnegative

theorem NonnegativeCoefficients.sum {I : Type*} (indices : Finset I) (polynomials : I → Polynomial ℝ)
    (nonnegative : ∀ index ∈ indices, NonnegativeCoefficients (polynomials index)) :
    NonnegativeCoefficients (∑ index ∈ indices, polynomials index) := by
  intro order
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg (fun index member => nonnegative index member order)

theorem NonnegativeCoefficients.comp {outer inner : Polynomial ℝ}
    (outerNonnegative : NonnegativeCoefficients outer) (innerNonnegative : NonnegativeCoefficients inner) :
    NonnegativeCoefficients (outer.comp inner) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum]
  exact NonnegativeCoefficients.sum outer.support _ (fun order _ =>
    (nonnegativeCoefficients_const _ (outerNonnegative order)).mul (innerNonnegative.pow order))

theorem NonnegativeCoefficients.linear_bound {polynomial : Polynomial ℝ}
    (nonnegative : NonnegativeCoefficients polynomial) (zero : polynomial.eval 0 = 0)
    {value : ℝ} (positive : 0 ≤ value) (small : value ≤ 1) :
    polynomial.eval value ≤ polynomial.eval 1 * value := by
  have coefficientZero : polynomial.coeff 0 = 0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using zero
  have term (order : ℕ) : polynomial.coeff order * value ^ order ≤ polynomial.coeff order * value := by
    cases order with
    | zero => simp [coefficientZero]
    | succ order =>
      apply mul_le_mul_of_nonneg_left _ (nonnegative (order + 1))
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ positive small) positive).trans_eq (one_mul value)
  calc
    polynomial.eval value = ∑ order ∈ polynomial.support, polynomial.coeff order * value ^ order := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
    _ ≤ ∑ order ∈ polynomial.support, polynomial.coeff order * value := Finset.sum_le_sum (fun order _ => term order)
    _ = (∑ order ∈ polynomial.support, polynomial.coeff order) * value := (Finset.sum_mul _ _ _).symm
    _ = polynomial.eval 1 * value := by simp only [Polynomial.eval_eq_sum, Polynomial.sum, one_pow, mul_one]

theorem comparisonPolynomialContract_of_nonnegative_zero (polynomials : ℕ → Polynomial ℝ)
    (nonnegative : ∀ grade, NonnegativeCoefficients (polynomials grade))
    (zero : ∀ grade, (polynomials grade).eval 0 = 0) : ComparisonPolynomialContract polynomials := by
  intro grade
  exact ⟨nonnegative grade, zero grade, (polynomials grade).eval 1,
    (nonnegative grade).eval_nonnegative zero_le_one,
    fun _ positive small => (nonnegative grade).linear_bound (zero grade) positive small⟩

def forwardComparisonPolynomial (L sigma gamma : ℝ) (grade : ℕ)
    (errorPolynomial gaugePolynomial : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (errorForwardConstant L sigma gamma grade * reconstructionBoundConstant L gamma grade) *
    errorPolynomial * (Polynomial.C 1 + (transferPolynomial L sigma gamma grade).comp gaugePolynomial)

theorem forwardComparisonPolynomial_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {errorPolynomial gaugePolynomial : Polynomial ℝ}
    (errorNonnegative : NonnegativeCoefficients errorPolynomial)
    (gaugeNonnegative : NonnegativeCoefficients gaugePolynomial) :
    NonnegativeCoefficients (forwardComparisonPolynomial L sigma gamma grade errorPolynomial gaugePolynomial) :=
  ((nonnegativeCoefficients_const _ (mul_nonneg (errorForwardConstant_nonnegative admissible grade)
    (reconstructionBoundConstant_nonnegative admissible grade))).mul errorNonnegative).mul
    ((nonnegativeCoefficients_const 1 zero_le_one).add
      ((transferPolynomial_nonnegative admissible grade).comp gaugeNonnegative))

theorem forwardComparisonPolynomial_zero (L sigma gamma : ℝ) (grade : ℕ)
    (errorPolynomial gaugePolynomial : Polynomial ℝ) (zero : errorPolynomial.eval 0 = 0) :
    (forwardComparisonPolynomial L sigma gamma grade errorPolynomial gaugePolynomial).eval 0 = 0 := by
  simp only [forwardComparisonPolynomial, Polynomial.eval_mul, zero, mul_zero, zero_mul]

theorem forwardComparisonPolynomial_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (data : LedgerData L sigma gamma ell) (errorPolynomial gaugePolynomial : Polynomial ℝ) (value : ℝ)
    (errorBound : errorCoefficientSize data (grade + 1) ≤ errorPolynomial.eval value)
    (gaugeBound : gaugeEpsilon (data.gaugeDeviation (grade + 3)) ≤ gaugePolynomial.eval value) :
    errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1) *
      reconstructionBoundConstant L gamma grade * completedTransferConstant data.gaugeDeviation grade ≤
        (forwardComparisonPolynomial L sigma gamma grade errorPolynomial gaugePolynomial).eval value := by
  have transferred : completedTransferConstant data.gaugeDeviation grade ≤
      1 + (transferPolynomial L sigma gamma grade).eval (gaugePolynomial.eval value) := by
    have bound := (transferPolynomial_nonnegative admissible grade).eval_monotone
      (gaugeEpsilon_nonnegative _) gaugeBound
    unfold completedTransferConstant
    linarith
  have errorPositive := (errorCoefficientSize_nonnegative data (grade + 1)).trans errorBound
  have first := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left errorBound (errorForwardConstant_nonnegative admissible grade))
    (reconstructionBoundConstant_nonnegative admissible grade)
  have total := mul_le_mul first transferred (completedTransferConstant_nonnegative admissible _ grade)
    (mul_nonneg (mul_nonneg (errorForwardConstant_nonnegative admissible grade) errorPositive)
      (reconstructionBoundConstant_nonnegative admissible grade))
  exact total.trans_eq (by
    simp only [forwardComparisonPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_comp]
    ring)

end Grad.GaugeCoefficients.Physical.Compensated
