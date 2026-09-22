import GQF36FluxPolynomial

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem polynomialControl_zero {E : Type*} [SeminormedAddCommGroup E]
    (polynomial : Polynomial ℝ) (value : ℝ) (actual : E)
    (nonnegative : NonnegativeCoefficients polynomial) (zero : polynomial.eval 0 = 0)
    (bound : ‖actual‖ ≤ polynomial.eval value) : PolynomialControl polynomial value actual 0 where
  nonnegative := nonnegative
  referenceBound := by rw [norm_zero, zero]
  deviationBound := by rw [sub_zero, zero, sub_zero]; exact bound

theorem inverseNormPolynomial_zero (grade : ℕ) (input : Polynomial ℝ) (zero : input.eval 0 = 0) :
    (inverseNormPolynomial grade input).eval 0 = (Fintype.card (DerivativeIndex grade) : ℝ) := by
  simp only [inverseNormPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    substitutedInversePolynomial_eval, zero, inverseSlotPolynomial_eval_zero, add_zero, mul_one]

theorem inverseFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (positive : 0 < dimension)
    (input : CoefficientFamily L sigma gamma ell dimension dimension) (coherent : FamilyCoherent input)
    (small : ‖input 0‖ ≤ 1 / 2) (grade : ℕ) (polynomial : Polynomial ℝ) (value : ℝ)
    (nonnegative : NonnegativeCoefficients polynomial) (zero : polynomial.eval 0 = 0)
    (bound : ‖input grade‖ ≤ polynomial.eval value) :
    PolynomialControl (inverseNormPolynomial grade polynomial) value
      (inverseFamily admissible input grade) (identityFamily L sigma gamma ell dimension grade) where
  nonnegative := inverseNormPolynomial_nonnegative grade nonnegative
  referenceBound := (identityFamily_norm_le L sigma gamma ell dimension grade).trans_eq
    (inverseNormPolynomial_zero grade polynomial zero).symm
  deviationBound := by
    have actual := (inverse_deviation_polynomial_bound admissible positive input coherent small grade).trans
      (mul_le_mul_of_nonneg_left ((inverseSlotPolynomial_nonnegative grade (grade + 1)).eval_monotone
        (norm_nonneg _) bound) (Nat.cast_nonneg _))
    exact actual.trans_eq (by
      rw [inverseNormPolynomial_zero grade polynomial zero]
      simp only [inverseNormPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        substitutedInversePolynomial_eval]
      ring)

def primitiveLinearPolynomial (grade : ℕ) : Polynomial ℝ :=
  linearBoundPolynomial (Fintype.card (DerivativeIndex grade) : ℝ)

theorem primitiveLinearPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (primitiveLinearPolynomial grade) :=
  linearBoundPolynomial_nonnegative (Nat.cast_nonneg _)

theorem primitiveLinearPolynomial_zero (grade : ℕ) : (primitiveLinearPolynomial grade).eval 0 = 0 := by
  rw [primitiveLinearPolynomial, linearBoundPolynomial_eval, mul_zero]

theorem primitive_component_bounds {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade ≤ high) :
    ‖actualFrameFamily parameters L ell epsilon base grade‖ ≤
        (primitiveLinearPolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) ∧
      ‖seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ ≤
        (primitiveLinearPolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) ∧
      ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter‖ ≤
        (primitiveLinearPolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) := by
  have frame := coherent_coefficient_grade_bound (actualFrameFamily parameters L ell epsilon base)
    (actualFrameFamily_coherent parameters admissible epsilon base) ordered
  have seed := coherent_coefficient_grade_bound (fun q => seedMatrixDeviationCoefficient admissible q rho alpha delta parameter)
    (seedDeviationFamily_coherent admissible rho alpha delta parameter) ordered
  have derivative := coherent_coefficient_grade_bound (fun q => seedDerivativeCoefficient admissible q rho alpha delta parameter)
    (seedDerivativeFamily_coherent admissible rho alpha delta parameter) ordered
  have first : ‖actualFrameFamily parameters L ell epsilon base high‖ ≤
      primitiveSize parameters admissible rho alpha delta parameter epsilon base high := by
    unfold primitiveSize
    linarith [norm_nonneg (seedMatrixDeviationCoefficient admissible high rho alpha delta parameter),
      norm_nonneg (seedDerivativeCoefficient admissible high rho alpha delta parameter)]
  have second : ‖seedMatrixDeviationCoefficient admissible high rho alpha delta parameter‖ ≤
      primitiveSize parameters admissible rho alpha delta parameter epsilon base high := by
    unfold primitiveSize
    linarith [norm_nonneg (actualFrameFamily parameters L ell epsilon base high),
      norm_nonneg (seedDerivativeCoefficient admissible high rho alpha delta parameter)]
  have third : ‖seedDerivativeCoefficient admissible high rho alpha delta parameter‖ ≤
      primitiveSize parameters admissible rho alpha delta parameter epsilon base high := by
    unfold primitiveSize
    linarith [norm_nonneg (actualFrameFamily parameters L ell epsilon base high),
      norm_nonneg (seedMatrixDeviationCoefficient admissible high rho alpha delta parameter)]
  refine ⟨?_, ?_, ?_⟩
  · exact (frame.trans (mul_le_mul_of_nonneg_left first (Nat.cast_nonneg _))).trans_eq (linearBoundPolynomial_eval _ _).symm
  · exact (seed.trans (mul_le_mul_of_nonneg_left second (Nat.cast_nonneg _))).trans_eq (linearBoundPolynomial_eval _ _).symm
  · exact (derivative.trans (mul_le_mul_of_nonneg_left third (Nat.cast_nonneg _))).trans_eq (linearBoundPolynomial_eval _ _).symm

def framePrimitivePolynomial (grade : ℕ) : Polynomial ℝ :=
  fixedCoefficientPolynomial referenceFrame grade + primitiveLinearPolynomial grade

def seedPrimitivePolynomial (grade : ℕ) : Polynomial ℝ := identityNormPolynomial grade + primitiveLinearPolynomial grade

theorem fullFrameFamily_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade ≤ high) :
    PolynomialControl (framePrimitivePolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (fullFrameFamily parameters L ell epsilon base grade) (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade) := by
  have error := polynomialControl_zero (primitiveLinearPolynomial grade) _
    (actualFrameFamily parameters L ell epsilon base grade) (primitiveLinearPolynomial_nonnegative grade)
    (primitiveLinearPolynomial_zero grade)
    (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base grade high ordered).1
  have total := (constantFamily_control admissible referenceFrame grade
    (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)).add error
  simpa only [framePrimitivePolynomial, fullFrameFamily, add_zero] using total

theorem seedMatrixFamily_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade ≤ high) :
    PolynomialControl (seedPrimitivePolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (seedMatrixFamily admissible rho alpha delta parameter grade) (identityFamily L parameters.sigma0 parameters.gamma ell 2 grade) := by
  have error := polynomialControl_zero (primitiveLinearPolynomial grade) _
    (seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) (primitiveLinearPolynomial_nonnegative grade)
    (primitiveLinearPolynomial_zero grade)
    (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base grade high ordered).2.1
  have total := (polynomialControl_constant (identityFamily L parameters.sigma0 parameters.gamma ell 2 grade)
    (Fintype.card (DerivativeIndex grade) : ℝ)
    (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
    (identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 2 grade)).add error
  simpa only [seedPrimitivePolynomial, seedMatrixFamily, identityNormPolynomial, identityFamily, add_zero] using total

end Grad.GaugeCoefficients.Physical.Compensated
