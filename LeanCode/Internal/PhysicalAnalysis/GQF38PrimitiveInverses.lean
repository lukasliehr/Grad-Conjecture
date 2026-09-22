import GQF37PrimitiveControls

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem fixedCoefficientPolynomial_nonnegative {input output : ℕ}
    (operator : OperatorValue input output) (grade : ℕ) :
    NonnegativeCoefficients (fixedCoefficientPolynomial operator grade) :=
  nonnegativeCoefficients_const _ (fixedFamilyConstant_nonnegative operator grade)

def frameInverseInputPolynomial (grade : ℕ) : Polynomial ℝ :=
  productPolynomial grade (fixedCoefficientPolynomial referenceFrame grade) (primitiveLinearPolynomial grade)

def frameInversePrimitivePolynomial (grade : ℕ) : Polynomial ℝ :=
  fixedCoefficientPolynomial referenceFrame grade +
    productPolynomial grade (deviationPolynomial (inverseNormPolynomial grade (frameInverseInputPolynomial grade)))
      (fixedCoefficientPolynomial referenceFrame grade)

def seedInversePrimitivePolynomial (grade : ℕ) : Polynomial ℝ := inverseNormPolynomial grade (primitiveLinearPolynomial grade)

theorem frameInverseInputPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (frameInverseInputPolynomial grade) :=
  productPolynomial_nonnegative grade (fixedCoefficientPolynomial_nonnegative _ grade) (primitiveLinearPolynomial_nonnegative grade)

theorem frameInverseInputPolynomial_zero (grade : ℕ) : (frameInverseInputPolynomial grade).eval 0 = 0 := by
  simp only [frameInverseInputPolynomial, productPolynomial, Polynomial.eval_mul, primitiveLinearPolynomial_zero, mul_zero]

theorem frameInversePrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (frameInversePrimitivePolynomial grade) :=
  (fixedCoefficientPolynomial_nonnegative _ grade).add
    (productPolynomial_nonnegative grade
      (deviationPolynomial_nonnegative (inverseNormPolynomial_nonnegative grade (frameInverseInputPolynomial_nonnegative grade)))
      (fixedCoefficientPolynomial_nonnegative _ grade))

theorem seedInversePrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (seedInversePrimitivePolynomial grade) :=
  inverseNormPolynomial_nonnegative grade (primitiveLinearPolynomial_nonnegative grade)

theorem actualFrameInverse_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3)
    (small : ‖frameInverseInput parameters admissible epsilon base 0‖ ≤ 1 / 4)
    (grade high : ℕ) (ordered : grade ≤ high) :
    PolynomialControl (frameInversePrimitivePolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (actualFrameInverse parameters admissible epsilon base grade)
      (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade) := by
  let value := primitiveSize parameters admissible rho alpha delta parameter epsilon base high
  have frameBound := (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base grade high ordered).1
  have inputBound : ‖frameInverseInput parameters admissible epsilon base grade‖ ≤
      (frameInverseInputPolynomial grade).eval value := by
    change ‖-coefficientComposition admissible grade _ _‖ ≤ _
    rw [norm_neg]
    exact productPolynomial_bound admissible _ _
      ((constantFamily_control admissible referenceFrame grade value).actualBound) frameBound
  have inverse := inverseFamily_control admissible (by norm_num : 0 < 3)
    (frameInverseInput parameters admissible epsilon base)
    (frameInverseInput_coherent parameters admissible epsilon base) (small.trans (by norm_num)) grade
    (frameInverseInputPolynomial grade) value (frameInverseInputPolynomial_nonnegative grade)
    (frameInverseInputPolynomial_zero grade) inputBound
  have fixed := constantFamily_control admissible referenceFrame grade value
  have total := fixed.add (inverse.deviation.comp admissible fixed)
  have zero : coefficientComposition admissible grade
      (0 : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3)
      (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade) = 0 :=
    map_zero (compositionLeftLinear admissible grade _)
  simpa only [frameInversePrimitivePolynomial, actualFrameInverse, actualFrameInverseDeviation,
    normalizedFrameInverse, identityFamily, value, zero, add_zero] using total

theorem actualSeedInverse_control {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3)
    (small : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade high : ℕ) (ordered : grade ≤ high) :
    PolynomialControl (seedInversePrimitivePolynomial grade)
      (primitiveSize parameters admissible rho alpha delta parameter epsilon base high)
      (actualSeedInverse admissible rho alpha delta parameter grade)
      (identityFamily L parameters.sigma0 parameters.gamma ell 2 grade) := by
  apply inverseFamily_control admissible (by norm_num : 0 < 2)
    (seedInverseInput admissible rho alpha delta parameter)
    (seedInverseInput_coherent admissible rho alpha delta parameter) (small.trans (by norm_num)) grade
    (primitiveLinearPolynomial grade) _ (primitiveLinearPolynomial_nonnegative grade) (primitiveLinearPolynomial_zero grade)
  change ‖-seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ ≤ _
  rw [norm_neg]
  exact (primitive_component_bounds parameters admissible rho alpha delta parameter epsilon base grade high ordered).2.1

end Grad.GaugeCoefficients.Physical.Compensated
