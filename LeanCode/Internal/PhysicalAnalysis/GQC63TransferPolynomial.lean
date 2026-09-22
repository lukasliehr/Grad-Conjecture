import GQC62GaugeEpsilon
import GQC50TransferGraphBounds

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

def transferPolynomialConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  Real.sqrt 5 * removedGraphConstant * apMultiplierConstant L sigma gamma (grade + 1) *
    apComplementConstant (grade + 1) * apMultiplierConstant L sigma gamma (grade + 1) *
      Fintype.card (DerivativeIndex (grade + 1)) * reconstructionBoundConstant L gamma grade

def transferPolynomial (L sigma gamma : ℝ) (grade : ℕ) : Polynomial ℝ :=
  Polynomial.C (transferPolynomialConstant L sigma gamma grade) * extensionNormPolynomial (grade + 1) * Polynomial.X

theorem transferPolynomialConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ transferPolynomialConstant L sigma gamma grade := by
  unfold transferPolynomialConstant
  positivity [removedGraphConstant_nonnegative, apMultiplierConstant_nonnegative admissible (grade + 1),
    apComplementConstant_nonnegative (grade + 1), reconstructionBoundConstant_nonnegative admissible grade]

theorem transferPolynomial_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : NonnegativeCoefficients (transferPolynomial L sigma gamma grade) :=
  ((nonnegativeCoefficients_const _ (transferPolynomialConstant_nonnegative admissible grade)).mul
    (extensionNormPolynomial_nonnegative (grade + 1))).mul nonnegativeCoefficients_X

theorem transferPolynomial_zero (L sigma gamma : ℝ) (grade : ℕ) : (transferPolynomial L sigma gamma grade).eval 0 = 0 := by
  simp only [transferPolynomial, Polynomial.eval_mul, Polynomial.eval_X, mul_zero]

/-- Exact AO22: epsilon is the sum of the four ORIGINAL gauge-block
coefficient norms at s+3; there is no larger physical-budget substitution. -/
theorem compensatedForward_polynomial_difference {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (small : ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2)
    (grade : ℕ) (large : 3 ≤ grade) (data : circularCompensatedCore admissible) :
    compensatedNorm admissible grade (compensatedForward admissible gauge coherent inverseCoherent data.val - data.val) ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) * compensatedNorm admissible grade data.val := by
  let q := grade + 1
  let size := gaugeEpsilon (gauge (grade + 3))
  let field := compensatedReconstruct admissible data.val
  let removed := apSmoothExtension admissible gauge coherent inverseCoherent (apSmoothGauge admissible gauge coherent field)
  have sizeNonnegative : 0 ≤ size := gaugeEpsilon_nonnegative _
  have highBound : ‖gauge (q + 2)‖ ≤ size := coefficient_norm_le_gaugeEpsilon _
  have lowBound : ‖gauge q‖ ≤ (Fintype.card (DerivativeIndex q) : ℝ) * size :=
    (coherent_coefficient_grade_bound gauge coherent (by omega : q ≤ q + 2)).trans
      (mul_le_mul_of_nonneg_left highBound (Nat.cast_nonneg _))
  have extensionBound : ‖complementExtensionFamily admissible gauge q‖ ≤ (extensionNormPolynomial q).eval size :=
    (extensionNormPolynomial_bound admissible gauge coherent small q).trans
      ((extensionNormPolynomial_nonnegative q).eval_monotone (norm_nonneg _) highBound)
  have circular : apComplement L sigma gamma ell q (apSmoothGrade L sigma gamma ell 3 q field) = 0 := by
    have smooth : apSmoothComplement L sigma gamma ell field = 0 := data.property.2
    exact (congrArg (apSmoothGrade L sigma gamma ell 3 q) smooth).trans (map_zero _)
  have gaugeBound := (apGaugeMap_circle_bound admissible gauge (by omega : 2 ≤ q) _ circular).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left lowBound (apMultiplierConstant_nonnegative admissible q))
        (apComplementConstant_nonnegative q))
      (compensatedReconstruct_bound admissible grade data.val) (norm_nonneg _)
      (mul_nonneg (apComplementConstant_nonnegative q)
        (mul_nonneg (apMultiplierConstant_nonnegative admissible q) (mul_nonneg (Nat.cast_nonneg _) sizeNonnegative))))
  have removedBound : ‖apSmoothGrade L sigma gamma ell 3 q removed‖ ≤
      (apMultiplierConstant L sigma gamma q * (extensionNormPolynomial q).eval size) *
        ((apComplementConstant q * (apMultiplierConstant L sigma gamma q * ((Fintype.card (DerivativeIndex q) : ℝ) * size))) *
          (reconstructionBoundConstant L gamma grade * compensatedNorm admissible grade data.val)) :=
    (apExtensionMap_bound admissible gauge q _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left extensionBound (apMultiplierConstant_nonnegative admissible q)) gaugeBound
        (norm_nonneg _) (mul_nonneg (apMultiplierConstant_nonnegative admissible q)
          ((extensionNormPolynomial_nonnegative q).eval_nonnegative sizeNonnegative)))
  have member : apSmoothGrade L sigma gamma ell 3 q removed ∈ apComplementRange L sigma gamma ell q := by
    have result := apSmoothCurrent_removed_mem admissible gauge coherent inverseCoherent laws field q
    change apSmoothGrade L sigma gamma ell 3 q (field - (field - removed)) ∈ _ at result
    simpa only [sub_sub_cancel] using result
  exact (compensatedNorm_remove_bound admissible grade data.val removed member).trans
    ((mul_le_mul_of_nonneg_left removedBound (mul_nonneg (Real.sqrt_nonneg _) removedGraphConstant_nonnegative)).trans_eq (by
      simp only [transferPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      unfold transferPolynomialConstant
      dsimp only [q, size]
      ring))

end Grad.GaugeCoefficients.Physical.Compensated
