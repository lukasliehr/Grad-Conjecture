import GQC63TransferPolynomial

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.GaugeTransfer

def transferLinearConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  transferPolynomialConstant L sigma gamma grade * (extensionNormPolynomial (grade + 1)).eval 1

theorem transferLinearConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ transferLinearConstant L sigma gamma grade :=
  mul_nonneg (transferPolynomialConstant_nonnegative admissible grade)
    ((extensionNormPolynomial_nonnegative (grade + 1)).eval_nonnegative zero_le_one)

theorem transferPolynomial_linear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {value : ℝ} (nonnegative : 0 ≤ value) (small : value ≤ 1) :
    (transferPolynomial L sigma gamma grade).eval value ≤ transferLinearConstant L sigma gamma grade * value := by
  have bound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((extensionNormPolynomial_nonnegative (grade + 1)).eval_monotone nonnegative small)
    (transferPolynomialConstant_nonnegative admissible grade)) nonnegative
  have formula : (transferPolynomial L sigma gamma grade).eval value =
      transferPolynomialConstant L sigma gamma grade * (extensionNormPolynomial (grade + 1)).eval value * value := by
    simp only [transferPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact formula.trans_le bound

theorem difference_factor (constant value : ℝ) : constant * value + value = (constant + 1) * value := by ring

theorem real_bound_of_difference (original transformed difference constant : ℝ)
    (triangle : transformed ≤ difference + original) (bound : difference ≤ constant * original) :
    transformed ≤ (constant + 1) * original :=
  triangle.trans ((add_le_add bound (le_refl original)).trans_eq (difference_factor constant original))

theorem compensatedNorm_bound_of_difference {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (original transformed : CompensatedData L sigma gamma ell) {constant : ℝ}
    (difference : compensatedNorm admissible grade (transformed - original) ≤ constant * compensatedNorm admissible grade original) :
    compensatedNorm admissible grade transformed ≤ (constant + 1) * compensatedNorm admissible grade original := by
  have equality : transformed = (transformed - original) + original := (sub_add_cancel transformed original).symm
  have triangle : compensatedNorm admissible grade transformed ≤
      compensatedNorm admissible grade (transformed - original) + compensatedNorm admissible grade original :=
    (congrArg (compensatedNorm admissible grade) equality).trans_le
      (compensatedNorm_triangle admissible grade (transformed - original) original)
  exact real_bound_of_difference (compensatedNorm admissible grade original)
    (compensatedNorm admissible grade transformed) (compensatedNorm admissible grade (transformed - original)) constant triangle difference

theorem compensatedCoreEquivalence_norm_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (small : ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2)
    (grade : ℕ) (large : 3 ≤ grade) (data : circularCompensatedCore admissible) :
    compensatedNorm admissible grade (compensatedCoreEquivalence admissible gauge coherent inverseCoherent laws data).val ≤
      ((transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) + 1) * compensatedNorm admissible grade data.val :=
  compensatedNorm_bound_of_difference admissible grade data.val _
    (compensatedForward_polynomial_difference admissible gauge coherent inverseCoherent laws small grade large data)

theorem compensatedCoreEquivalence_inverse_norm_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (grade : ℕ) (data : currentCompensatedCore admissible gauge coherent) :
    compensatedNorm admissible grade ((compensatedCoreEquivalence admissible gauge coherent inverseCoherent laws).symm data).val ≤
      (backwardDifferenceConstant grade + 1) * compensatedNorm admissible grade data.val :=
  compensatedNorm_bound_of_difference admissible grade data.val _ (compensatedBackward_difference_bound admissible grade data.val)

end Grad.GaugeCoefficients.Physical.Compensated
