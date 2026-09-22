import GQF32ComparisonPolynomials

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- Same-grade finite polynomial accounting. The constant term bounds the
literal reference; the nonconstant part bounds the actual deviation. -/
structure PolynomialControl {E : Type*} [SeminormedAddCommGroup E]
    (polynomial : Polynomial ℝ) (value : ℝ) (actual reference : E) : Prop where
  nonnegative : NonnegativeCoefficients polynomial
  referenceBound : ‖reference‖ ≤ polynomial.eval 0
  deviationBound : ‖actual - reference‖ ≤ polynomial.eval value - polynomial.eval 0

theorem PolynomialControl.actualBound {E : Type*} [SeminormedAddCommGroup E]
    {polynomial : Polynomial ℝ} {value : ℝ} {actual reference : E}
    (control : PolynomialControl polynomial value actual reference) : ‖actual‖ ≤ polynomial.eval value := by
  have bound := (norm_le_norm_sub_add actual reference).trans
    (add_le_add control.deviationBound control.referenceBound)
  exact bound.trans_eq (sub_add_cancel _ _)

theorem PolynomialControl.deviation_nonnegative {E : Type*} [SeminormedAddCommGroup E]
    {polynomial : Polynomial ℝ} {value : ℝ} {actual reference : E}
    (control : PolynomialControl polynomial value actual reference) : 0 ≤ polynomial.eval value - polynomial.eval 0 :=
  (norm_nonneg _).trans control.deviationBound

theorem polynomialControl_constant {E : Type*} [SeminormedAddCommGroup E]
    (actual : E) (constant value : ℝ) (bound : ‖actual‖ ≤ constant) :
    PolynomialControl (Polynomial.C constant) value actual actual where
  nonnegative := nonnegativeCoefficients_const _ ((norm_nonneg _).trans bound)
  referenceBound := bound.trans_eq (Polynomial.eval_C).symm
  deviationBound := by simp only [sub_self, norm_zero, Polynomial.eval_C]; exact le_rfl

theorem PolynomialControl.add {E : Type*} [SeminormedAddCommGroup E]
    {firstP secondP : Polynomial ℝ} {value : ℝ} {first referenceFirst second referenceSecond : E}
    (firstControl : PolynomialControl firstP value first referenceFirst)
    (secondControl : PolynomialControl secondP value second referenceSecond) :
    PolynomialControl (firstP + secondP) value (first + second) (referenceFirst + referenceSecond) where
  nonnegative := firstControl.nonnegative.add secondControl.nonnegative
  referenceBound := (norm_add_le _ _).trans
    ((add_le_add firstControl.referenceBound secondControl.referenceBound).trans_eq (Polynomial.eval_add).symm)
  deviationBound := by
    have difference : (first + second) - (referenceFirst + referenceSecond) =
        (first - referenceFirst) + (second - referenceSecond) := by abel
    exact (congrArg norm difference).le.trans ((norm_add_le _ _).trans
      ((add_le_add firstControl.deviationBound secondControl.deviationBound).trans_eq (by
        simp only [Polynomial.eval_add]
        ring)))

theorem PolynomialControl.smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {polynomial : Polynomial ℝ} {value : ℝ} {actual reference : E}
    (control : PolynomialControl polynomial value actual reference) (scalar : ℂ) :
    PolynomialControl (Polynomial.C ‖scalar‖ * polynomial) value (scalar • actual) (scalar • reference) where
  nonnegative := (nonnegativeCoefficients_const _ (norm_nonneg _)).mul control.nonnegative
  referenceBound := (norm_smul scalar reference).le.trans
    ((mul_le_mul_of_nonneg_left control.referenceBound (norm_nonneg _)).trans_eq (by
      simp only [Polynomial.eval_mul, Polynomial.eval_C]))
  deviationBound := by
    rw [← smul_sub, norm_smul]
    exact (mul_le_mul_of_nonneg_left control.deviationBound (norm_nonneg _)).trans_eq (by
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring)

theorem PolynomialControl.finiteSum {E I : Type*} [SeminormedAddCommGroup E] [Fintype I]
    (polynomials : I → Polynomial ℝ) (value : ℝ) (actual reference : I → E)
    (controls : ∀ index, PolynomialControl (polynomials index) value (actual index) (reference index)) :
    PolynomialControl (∑ index, polynomials index) value (∑ index, actual index) (∑ index, reference index) where
  nonnegative := NonnegativeCoefficients.sum Finset.univ _ (fun index _ => (controls index).nonnegative)
  referenceBound := (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun index _ => (controls index).referenceBound)).trans_eq
    (by simp only [Polynomial.eval_finsetSum]))
  deviationBound := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun index _ => (controls index).deviationBound)).trans_eq
      (by simp only [Polynomial.eval_finsetSum, Finset.sum_sub_distrib]))

theorem PolynomialControl.comp {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input middle output : ℕ} {outerP innerP : Polynomial ℝ} {value : ℝ}
    {outer referenceOuter : Coefficient L sigma gamma ell grade middle output}
    {inner referenceInner : Coefficient L sigma gamma ell grade input middle}
    (outerControl : PolynomialControl outerP value outer referenceOuter)
    (innerControl : PolynomialControl innerP value inner referenceInner) :
    PolynomialControl (productPolynomial grade outerP innerP) value
      (coefficientComposition admissible grade outer inner)
      (coefficientComposition admissible grade referenceOuter referenceInner) where
  nonnegative := productPolynomial_nonnegative grade outerControl.nonnegative innerControl.nonnegative
  referenceBound := productPolynomial_bound admissible _ _ outerControl.referenceBound innerControl.referenceBound
  deviationBound := by
    have outerZero := outerControl.nonnegative.eval_nonnegative (le_refl (0 : ℝ))
    have innerZero := innerControl.nonnegative.eval_nonnegative (le_refl (0 : ℝ))
    have first := (coefficientComposition_norm_le admissible grade (outer - referenceOuter) referenceInner).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left outerControl.deviationBound (gradeProductConstant_nonnegative grade))
        innerControl.referenceBound (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
          outerControl.deviation_nonnegative))
    have second := (coefficientComposition_norm_le admissible grade referenceOuter (inner - referenceInner)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left outerControl.referenceBound (gradeProductConstant_nonnegative grade))
        innerControl.deviationBound (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade) outerZero))
    have third := (coefficientComposition_norm_le admissible grade (outer - referenceOuter) (inner - referenceInner)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left outerControl.deviationBound (gradeProductConstant_nonnegative grade))
        innerControl.deviationBound (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
          outerControl.deviation_nonnegative))
    rw [composition_deviation_expansion]
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add first second) third).trans_eq (by
        simp only [productPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
        ring)))

end Grad.GaugeCoefficients.Physical.Compensated
