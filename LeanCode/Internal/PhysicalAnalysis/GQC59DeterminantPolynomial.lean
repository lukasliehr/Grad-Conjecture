import GQC58CoefficientPolynomialAlgebra

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem determinantFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (RadialLedger.determinantFamily admissible gauge) :=
  (((identityFamily_coherent L sigma gamma ell 1).add (muDeviation_coherent admissible gauge coherent)).comp admissible
    ((identityFamily_coherent L sigma gamma ell 1).add (deltaDeviation_coherent admissible gauge coherent))).sub
      (((tangentRow_coherent L sigma gamma ell).comp admissible (tangentColumn_coherent L sigma gamma ell)).comp admissible
        ((etaCoefficient_coherent admissible gauge coherent).comp admissible (nuCoefficient_coherent admissible gauge coherent)))

def muNormPolynomial (grade : ℕ) : Polynomial ℝ := identityNormPolynomial grade + linearBoundPolynomial (muConstant (fun _ => 1) grade)
def etaNormPolynomial (grade : ℕ) : Polynomial ℝ := linearBoundPolynomial (etaConstant (fun _ => 1) grade)
def nuNormPolynomial (grade : ℕ) : Polynomial ℝ := linearBoundPolynomial (nuConstant (fun _ => 1) grade)
def deltaNormPolynomial (grade : ℕ) : Polynomial ℝ := identityNormPolynomial grade + linearBoundPolynomial (deltaDirectConstant grade)
def radiusNormPolynomial (grade : ℕ) : Polynomial ℝ :=
  productPolynomial grade (Polynomial.C (tangentRowConstant grade)) (Polynomial.C (tangentColumnConstant grade))
def determinantInputPolynomial (grade : ℕ) : Polynomial ℝ := identityNormPolynomial grade +
  (productPolynomial grade (muNormPolynomial grade) (deltaNormPolynomial grade) +
    productPolynomial grade (radiusNormPolynomial grade) (productPolynomial grade (etaNormPolynomial grade) (nuNormPolynomial grade)))

theorem muNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (muNormPolynomial grade) :=
  (identityNormPolynomial_nonnegative grade).add (linearBoundPolynomial_nonnegative (muConstant_nonnegative (fun _ => zero_le_one) grade))
theorem etaNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (etaNormPolynomial grade) :=
  linearBoundPolynomial_nonnegative (etaConstant_nonnegative (fun _ => zero_le_one) grade)
theorem nuNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (nuNormPolynomial grade) :=
  linearBoundPolynomial_nonnegative (nuConstant_nonnegative (fun _ => zero_le_one) grade)
theorem deltaNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (deltaNormPolynomial grade) :=
  (identityNormPolynomial_nonnegative grade).add (linearBoundPolynomial_nonnegative (deltaDirectConstant_nonnegative grade))
theorem radiusNormPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (radiusNormPolynomial grade) :=
  productPolynomial_nonnegative grade (nonnegativeCoefficients_const _ (tangentRowConstant_nonnegative grade))
    (nonnegativeCoefficients_const _ (tangentColumnConstant_nonnegative grade))
theorem determinantInputPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (determinantInputPolynomial grade) :=
  (identityNormPolynomial_nonnegative grade).add
    ((productPolynomial_nonnegative grade (muNormPolynomial_nonnegative grade) (deltaNormPolynomial_nonnegative grade)).add
      (productPolynomial_nonnegative grade (radiusNormPolynomial_nonnegative grade)
        (productPolynomial_nonnegative grade (etaNormPolynomial_nonnegative grade) (nuNormPolynomial_nonnegative grade))))

theorem muNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖muCoefficient admissible gauge grade‖ ≤ (muNormPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  polynomial_add_norm_bound _ _ (identityNormPolynomial_bound L sigma gamma ell 1 grade _)
    (linearBoundPolynomial_bound _ (muDeviation_coefficient_bound admissible gauge grade))
theorem etaNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖etaCoefficient admissible gauge grade‖ ≤ (etaNormPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  linearBoundPolynomial_bound _ (eta_coefficient_bound admissible gauge grade)
theorem nuNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖nuCoefficient admissible gauge grade‖ ≤ (nuNormPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  linearBoundPolynomial_bound _ (nu_coefficient_bound admissible gauge grade)
theorem deltaNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) :
    ‖deltaCoefficient admissible gauge grade‖ ≤ (deltaNormPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  polynomial_add_norm_bound _ _ (identityNormPolynomial_bound L sigma gamma ell 1 grade _)
    (linearBoundPolynomial_bound _ (deltaDeviation_coefficient_bound admissible gauge coherent grade))
theorem radiusNormPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (value : ℝ) :
    ‖radiusSquaredFamily admissible grade‖ ≤ (radiusNormPolynomial grade).eval value :=
  productPolynomial_bound admissible _ _ (constantPolynomial_bound _ (tangentRow_bound L sigma gamma ell grade) value)
    (constantPolynomial_bound _ (tangentColumn_bound L sigma gamma ell grade) value)

theorem determinantInputPolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) :
    ‖determinantInverseInput admissible gauge grade‖ ≤ (determinantInputPolynomial grade).eval ‖gauge (grade + 2)‖ :=
  polynomial_sub_norm_bound _ _ (identityNormPolynomial_bound L sigma gamma ell 1 grade _)
    (polynomial_sub_norm_bound _ _
      (productPolynomial_bound admissible _ _ (muNormPolynomial_bound admissible gauge grade) (deltaNormPolynomial_bound admissible gauge coherent grade))
      (productPolynomial_bound admissible _ _ (radiusNormPolynomial_bound admissible grade _)
        (productPolynomial_bound admissible _ _ (etaNormPolynomial_bound admissible gauge grade) (nuNormPolynomial_bound admissible gauge grade))))

def determinantInversePolynomial (grade : ℕ) : Polynomial ℝ := inverseNormPolynomial grade (determinantInputPolynomial grade)
theorem determinantInversePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (determinantInversePolynomial grade) :=
  inverseNormPolynomial_nonnegative grade (determinantInputPolynomial_nonnegative grade)

theorem determinantInversePolynomial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (small : ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2) (grade : ℕ) :
    ‖determinantInverseFamily admissible gauge grade‖ ≤ (determinantInversePolynomial grade).eval ‖gauge (grade + 2)‖ :=
  inverseNormPolynomial_bound admissible (by norm_num) (determinantInverseInput admissible gauge)
    ((identityFamily_coherent L sigma gamma ell 1).sub (determinantFamily_coherent admissible gauge coherent)) small grade _ _
    (determinantInputPolynomial_bound admissible gauge coherent grade)

end Grad.GaugeCoefficients.Physical.Compensated
