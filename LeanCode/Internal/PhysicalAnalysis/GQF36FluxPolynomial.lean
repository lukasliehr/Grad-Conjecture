import GQF35GaugeTracePolynomials

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def determinantTermPolynomial (grade : ℕ) (term : Fin 6) (polynomial : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade
    (productPolynomial grade
      (scalarEntryRecipePolynomial grade (0 : Fin 3) (determinantPermutation term).1 polynomial)
      (scalarEntryRecipePolynomial grade (1 : Fin 3) (determinantPermutation term).2.1 polynomial))
    (scalarEntryRecipePolynomial grade (2 : Fin 3) (determinantPermutation term).2.2 polynomial)

def determinantRecipePolynomial (grade : ℕ) (polynomial : Polynomial ℝ) : Polynomial ℝ :=
  ∑ term : Fin 6, Polynomial.C ‖determinantSign term‖ * determinantTermPolynomial grade term polynomial

theorem determinantFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} {polynomial : Polynomial ℝ} {value : ℝ}
    {actual reference : CoefficientFamily L sigma gamma ell 3 3}
    (control : PolynomialControl polynomial value (actual grade) (reference grade)) :
    PolynomialControl (determinantRecipePolynomial grade polynomial) value
      (determinantFamily admissible actual grade) (determinantFamily admissible reference grade) :=
  PolynomialControl.finiteSum _ _ _ _ (fun term =>
    (((scalarEntryFamily_control admissible 0 (determinantPermutation term).1 control).comp admissible
      (scalarEntryFamily_control admissible 1 (determinantPermutation term).2.1 control)).comp admissible
      (scalarEntryFamily_control admissible 2 (determinantPermutation term).2.2 control)).smul (determinantSign term))

def fluxRecipePolynomial (grade : ℕ) (frame inverse : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade (scalarLiftRecipePolynomial grade 3 (determinantRecipePolynomial grade frame))
    (productPolynomial grade inverse (transposeRecipePolynomial grade 3 3 inverse))

theorem fluxFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} {frameP inverseP : Polynomial ℝ} {value : ℝ}
    {frame referenceFrame inverse referenceInverse : CoefficientFamily L sigma gamma ell 3 3}
    (frameControl : PolynomialControl frameP value (frame grade) (referenceFrame grade))
    (inverseControl : PolynomialControl inverseP value (inverse grade) (referenceInverse grade)) :
    PolynomialControl (fluxRecipePolynomial grade frameP inverseP) value
      (fluxFamily admissible frame inverse grade) (fluxFamily admissible referenceFrame referenceInverse grade) :=
  (scalarLiftFamily_control admissible 3 (determinantFamily_control admissible frameControl)).comp admissible
    (inverseControl.comp admissible (transposeFamily_control admissible inverseControl))

def deviationPolynomial (polynomial : Polynomial ℝ) : Polynomial ℝ := polynomial - Polynomial.C (polynomial.eval 0)

theorem deviationPolynomial_nonnegative {polynomial : Polynomial ℝ}
    (nonnegative : NonnegativeCoefficients polynomial) : NonnegativeCoefficients (deviationPolynomial polynomial) := by
  intro order
  by_cases zero : order = 0
  · subst order
    change 0 ≤ (polynomial - Polynomial.C (polynomial.eval 0)).coeff 0
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero, sub_self]
  · simpa only [deviationPolynomial, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg zero, sub_zero] using nonnegative order

theorem deviationPolynomial_zero (polynomial : Polynomial ℝ) : (deviationPolynomial polynomial).eval 0 = 0 := by
  simp only [deviationPolynomial, Polynomial.eval_sub, Polynomial.eval_C, sub_self]

theorem deviationPolynomial_eval (polynomial : Polynomial ℝ) (value : ℝ) :
    (deviationPolynomial polynomial).eval value = polynomial.eval value - polynomial.eval 0 := by
  simp only [deviationPolynomial, Polynomial.eval_sub, Polynomial.eval_C]

theorem PolynomialControl.deviation {E : Type*} [SeminormedAddCommGroup E]
    {polynomial : Polynomial ℝ} {value : ℝ} {actual reference : E}
    (control : PolynomialControl polynomial value actual reference) :
    PolynomialControl (deviationPolynomial polynomial) value (actual - reference) 0 where
  nonnegative := deviationPolynomial_nonnegative control.nonnegative
  referenceBound := by rw [norm_zero, deviationPolynomial_zero]
  deviationBound := by
    rw [sub_zero, deviationPolynomial_zero, sub_zero, deviationPolynomial_eval]
    exact control.deviationBound

end Grad.GaugeCoefficients.Physical.Compensated
