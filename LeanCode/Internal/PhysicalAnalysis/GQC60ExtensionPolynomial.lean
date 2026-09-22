import GQC59DeterminantPolynomial

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

def liftedNormPolynomial (grade : ℕ) (row column : Fin 3) (scalar : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade (Polynomial.C (fixedFamilyConstant (matrixUnit (input := 1) row 0) grade))
    (productPolynomial grade scalar (Polynomial.C (fixedFamilyConstant (matrixUnit (output := 1) 0 column) grade)))

theorem liftedNormPolynomial_nonnegative (grade : ℕ) (row column : Fin 3) {scalar : Polynomial ℝ}
    (positive : NonnegativeCoefficients scalar) : NonnegativeCoefficients (liftedNormPolynomial grade row column scalar) :=
  productPolynomial_nonnegative grade (nonnegativeCoefficients_const _ (fixedFamilyConstant_nonnegative _ grade))
    (productPolynomial_nonnegative grade positive (nonnegativeCoefficients_const _ (fixedFamilyConstant_nonnegative _ grade)))

theorem liftedNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (row column : Fin 3) (scalar : CoefficientFamily L sigma gamma ell 1 1)
    {polynomial : Polynomial ℝ} {value : ℝ} (bound : ‖scalar grade‖ ≤ polynomial.eval value) :
    ‖liftedEntry admissible row column scalar grade‖ ≤ (liftedNormPolynomial grade row column polynomial).eval value :=
  productPolynomial_bound admissible _ _ (constantPolynomial_bound _ (constantFamily_norm_le admissible _ grade) value)
    (productPolynomial_bound admissible _ _ bound (constantPolynomial_bound _ (constantFamily_norm_le admissible _ grade) value))

def scalarLiftNormPolynomial (grade : ℕ) (scalar : Polynomial ℝ) : Polynomial ℝ :=
  liftedNormPolynomial grade 0 0 scalar + liftedNormPolynomial grade 1 1 scalar + liftedNormPolynomial grade 2 2 scalar

theorem scalarLiftNormPolynomial_nonnegative (grade : ℕ) {scalar : Polynomial ℝ}
    (positive : NonnegativeCoefficients scalar) : NonnegativeCoefficients (scalarLiftNormPolynomial grade scalar) :=
  ((liftedNormPolynomial_nonnegative grade 0 0 positive).add (liftedNormPolynomial_nonnegative grade 1 1 positive)).add
    (liftedNormPolynomial_nonnegative grade 2 2 positive)

theorem scalarLiftNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (scalar : CoefficientFamily L sigma gamma ell 1 1) {polynomial : Polynomial ℝ} {value : ℝ}
    (bound : ‖scalar grade‖ ≤ polynomial.eval value) :
    ‖scalarLiftFamily admissible 3 scalar grade‖ ≤ (scalarLiftNormPolynomial grade polynomial).eval value := by
  have result := polynomial_add_norm_bound _ _
    (polynomial_add_norm_bound _ _ (liftedNormPolynomial_bound admissible grade 0 0 scalar bound)
      (liftedNormPolynomial_bound admissible grade 1 1 scalar bound))
    (liftedNormPolynomial_bound admissible grade 2 2 scalar bound)
  have formula : scalarLiftFamily admissible 3 scalar grade =
      liftedEntry admissible 0 0 scalar grade + liftedEntry admissible 1 1 scalar grade + liftedEntry admissible 2 2 scalar grade :=
    Fin.sum_univ_three _
  exact (congrArg norm formula).trans_le result

def firstCrossPolynomial (grade : ℕ) : Polynomial ℝ :=
  productPolynomial grade (Polynomial.C (tangentColumnConstant grade))
    (productPolynomial grade (etaNormPolynomial grade) (Polynomial.C (scalarRowConstant grade)))
def secondCrossPolynomial (grade : ℕ) : Polynomial ℝ :=
  productPolynomial grade (Polynomial.C (scalarColumnConstant grade))
    (productPolynomial grade (nuNormPolynomial grade) (Polynomial.C (tangentRowConstant grade)))
def adjugateNormPolynomial (grade : ℕ) : Polynomial ℝ :=
  ((liftedNormPolynomial grade 0 0 (deltaNormPolynomial grade) + liftedNormPolynomial grade 1 1 (deltaNormPolynomial grade) +
    liftedNormPolynomial grade 2 2 (muNormPolynomial grade)) + firstCrossPolynomial grade) + secondCrossPolynomial grade

theorem adjugateNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (adjugateNormPolynomial grade) := by
  have diagonal := ((liftedNormPolynomial_nonnegative grade 0 0 (deltaNormPolynomial_nonnegative grade)).add
    (liftedNormPolynomial_nonnegative grade 1 1 (deltaNormPolynomial_nonnegative grade))).add
      (liftedNormPolynomial_nonnegative grade 2 2 (muNormPolynomial_nonnegative grade))
  have first := productPolynomial_nonnegative grade (nonnegativeCoefficients_const _ (tangentColumnConstant_nonnegative grade))
    (productPolynomial_nonnegative grade (etaNormPolynomial_nonnegative grade) (nonnegativeCoefficients_const _ (scalarRowConstant_nonnegative grade)))
  have second := productPolynomial_nonnegative grade (nonnegativeCoefficients_const _ (scalarColumnConstant_nonnegative grade))
    (productPolynomial_nonnegative grade (nuNormPolynomial_nonnegative grade) (nonnegativeCoefficients_const _ (tangentRowConstant_nonnegative grade)))
  exact (diagonal.add first).add second

theorem adjugateNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) :
    ‖adjugateFamily admissible gauge grade‖ ≤ (adjugateNormPolynomial grade).eval ‖gauge (grade + 2)‖ := by
  have mu := muNormPolynomial_bound admissible gauge grade
  have delta := deltaNormPolynomial_bound admissible gauge coherent grade
  have diagonal := polynomial_add_norm_bound _ _
    (polynomial_add_norm_bound _ _ (liftedNormPolynomial_bound admissible grade 0 0 _ delta)
      (liftedNormPolynomial_bound admissible grade 1 1 _ delta))
    (liftedNormPolynomial_bound admissible grade 2 2 _ mu)
  have first := productPolynomial_bound admissible _ _ (constantPolynomial_bound _ (tangentColumn_bound L sigma gamma ell grade) _)
    (productPolynomial_bound admissible _ _ (etaNormPolynomial_bound admissible gauge grade)
      (constantPolynomial_bound _ (scalarRow_bound admissible grade) _))
  have second := productPolynomial_bound admissible _ _ (constantPolynomial_bound _ (scalarColumn_bound admissible grade) _)
    (productPolynomial_bound admissible _ _ (nuNormPolynomial_bound admissible gauge grade)
      (constantPolynomial_bound _ (tangentRow_bound L sigma gamma ell grade) _))
  exact polynomial_sub_norm_bound _ _ (polynomial_sub_norm_bound _ _ diagonal first) second

def extensionNormPolynomial (grade : ℕ) : Polynomial ℝ :=
  productPolynomial grade (scalarLiftNormPolynomial grade (determinantInversePolynomial grade)) (adjugateNormPolynomial grade)

theorem extensionNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (extensionNormPolynomial grade) :=
  productPolynomial_nonnegative grade (scalarLiftNormPolynomial_nonnegative grade (determinantInversePolynomial_nonnegative grade))
    (adjugateNormPolynomial_nonnegative grade)

/-- Literal nonsingular Etilde formula, bounded by a finite polynomial in
the actual gauge coefficient grade q+2, uniformly in ell. -/
theorem extensionNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (small : ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2) (grade : ℕ) :
    ‖complementExtensionFamily admissible gauge grade‖ ≤ (extensionNormPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  productPolynomial_bound admissible _ _
    (scalarLiftNormPolynomial_bound admissible grade _ (determinantInversePolynomial_bound admissible gauge coherent small grade))
    (adjugateNormPolynomial_bound admissible gauge coherent grade)

end Grad.GaugeCoefficients.Physical.Compensated
