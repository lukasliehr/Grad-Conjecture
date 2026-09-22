import GQF39RecipePositivity

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Neumann.Regularity

def rotatedPrimitiveConstant (grade : ℕ) : ℝ :=
  (gradeProductConstant grade * coordinateIdentityConstant 1 grade +
    gradeProductConstant grade * coordinateIdentityConstant 0 grade) *
      (Fintype.card (DerivativeIndex grade) : ℝ) * (Fintype.card (DerivativeIndex (grade + 1)) : ℝ)

theorem rotatedPrimitiveConstant_nonnegative (grade : ℕ) : 0 ≤ rotatedPrimitiveConstant grade := by
  exact mul_nonneg (mul_nonneg (add_nonneg
    (mul_nonneg (gradeProductConstant_nonnegative grade) (coordinateIdentityConstant_nonnegative 1 grade))
    (mul_nonneg (gradeProductConstant_nonnegative grade) (coordinateIdentityConstant_nonnegative 0 grade)))
    (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

def rotatedPrimitivePolynomial (grade : ℕ) : Polynomial ℝ := linearBoundPolynomial (rotatedPrimitiveConstant grade)

theorem rotatedPrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (rotatedPrimitivePolynomial grade) :=
  linearBoundPolynomial_nonnegative (rotatedPrimitiveConstant_nonnegative grade)

theorem rotatedPrimitivePolynomial_zero (grade : ℕ) : (rotatedPrimitivePolynomial grade).eval 0 = 0 := by
  rw [rotatedPrimitivePolynomial, linearBoundPolynomial_eval, mul_zero]

theorem seedDerivative_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade ≤ high) :
    PolynomialControl (primitiveLinearPolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (seedDerivativeCoefficient admissible grade rho alpha delta parameter)
      (zeroFamily L parameters.sigma0 parameters.gamma ell 2 2 grade) :=
  polynomialControl_zero _ _ _ (primitiveLinearPolynomial_nonnegative grade) (primitiveLinearPolynomial_zero grade)
    (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base grade high ordered).2.2

theorem actualRotatedFrame_primitive_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade + 1 ≤ high) :
    ‖actualRotatedFrame parameters admissible epsilon base grade‖ ≤
      (rotatedPrimitivePolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) := by
  let value := primitiveSize parameters admissible rho alpha delta parameter epsilon base high
  have frameBound := (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base (grade + 1) high ordered).1
  have frameBound' : ‖actualFrameFamily parameters L ell epsilon base (grade + 1)‖ ≤
      (Fintype.card (DerivativeIndex (grade + 1)) : ℝ) * value := by
    simpa only [primitiveLinearPolynomial, linearBoundPolynomial_eval] using frameBound
  have derivativeBound (fixed : CartesianMultiIndex) (order : cartesianOrder fixed = 1) :
      ‖derivativeFamily fixed (actualFrameFamily parameters L ell epsilon base) grade‖ ≤
        (Fintype.card (DerivativeIndex grade) : ℝ) *
          ((Fintype.card (DerivativeIndex (grade + 1)) : ℝ) * value) := by
    have derivative := coefficientDerivativeShift_norm_le L parameters.sigma0 parameters.gamma ell grade 3 3 fixed
      (actualFrameFamily parameters L ell epsilon base (grade + cartesianOrder fixed))
    have inputNorm : ‖actualFrameFamily parameters L ell epsilon base (grade + cartesianOrder fixed)‖ =
        ‖actualFrameFamily parameters L ell epsilon base (grade + 1)‖ :=
      congrArg (fun q => ‖actualFrameFamily parameters L ell epsilon base q‖) (congrArg (Nat.add grade) order)
    exact derivative.trans (mul_le_mul_of_nonneg_left (inputNorm.le.trans frameBound') (Nat.cast_nonneg _))
  have each (direction : Fin 2) (fixed : CartesianMultiIndex) (order : cartesianOrder fixed = 1) :
      ‖coefficientComposition admissible grade
        (coordinateIdentityFamily L parameters.sigma0 parameters.gamma ell direction grade)
        (derivativeFamily fixed (actualFrameFamily parameters L ell epsilon base) grade)‖ ≤
        (gradeProductConstant grade * coordinateIdentityConstant direction grade) *
          ((Fintype.card (DerivativeIndex grade) : ℝ) * ((Fintype.card (DerivativeIndex (grade + 1)) : ℝ) * value)) :=
    (coefficientComposition_norm_le admissible grade _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left
        (coordinateIdentityFamily_bound L parameters.sigma0 parameters.gamma ell direction grade)
        (gradeProductConstant_nonnegative grade)) (derivativeBound fixed order) (norm_nonneg _)
        (mul_nonneg (gradeProductConstant_nonnegative grade) (coordinateIdentityConstant_nonnegative direction grade)))
  change ‖-coefficientComposition admissible grade _ _ + coefficientComposition admissible grade _ _‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact (add_le_add (each 1 (1, 0) rfl) (each 0 (0, 1) rfl)).trans_eq (by
    rw [rotatedPrimitivePolynomial, linearBoundPolynomial_eval]
    unfold rotatedPrimitiveConstant
    ring)

theorem actualRotatedFrame_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3) (grade high : ℕ) (ordered : grade + 1 ≤ high) :
    PolynomialControl (rotatedPrimitivePolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (actualRotatedFrame parameters admissible epsilon base grade)
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3 grade) :=
  polynomialControl_zero _ _ _ (rotatedPrimitivePolynomial_nonnegative grade) (rotatedPrimitivePolynomial_zero grade)
    (actualRotatedFrame_primitive_bound parameters admissible rho alpha delta parameter epsilon base grade high ordered)

end Grad.GaugeCoefficients.Physical.Compensated
