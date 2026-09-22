import GQF40RotatedPrimitive

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

def gaugePrimitivePolynomial (grade : ℕ) : Polynomial ℝ :=
  Polynomial.C 4 * deviationPolynomial (gaugeRecipePolynomial grade (seedPrimitivePolynomial grade)
    (primitiveLinearPolynomial grade) (frameInversePrimitivePolynomial grade))

def errorPrimitivePolynomial (grade : ℕ) : Polynomial ℝ :=
  deviationPolynomial (rotatedRecipePolynomial grade planarFrameColumns
      (rotatedPrimitivePolynomial grade) (frameInversePrimitivePolynomial grade)) +
    deviationPolynomial (fluxRecipePolynomial grade (framePrimitivePolynomial grade) (frameInversePrimitivePolynomial grade)) +
    deviationPolynomial (rotatedRecipePolynomial grade thirdFrameColumn
      (rotatedPrimitivePolynomial grade) (frameInversePrimitivePolynomial grade)) +
    deviationPolynomial (traceRecipePolynomial grade (seedInversePrimitivePolynomial grade) (frameInversePrimitivePolynomial grade))

theorem gaugePrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (gaugePrimitivePolynomial grade) :=
  (nonnegativeCoefficients_const 4 (by norm_num)).mul (deviationPolynomial_nonnegative
    (gaugeRecipePolynomial_nonnegative grade (seedPrimitivePolynomial_nonnegative grade)
      (primitiveLinearPolynomial_nonnegative grade) (frameInversePrimitivePolynomial_nonnegative grade)))

theorem gaugePrimitivePolynomial_zero (grade : ℕ) : (gaugePrimitivePolynomial grade).eval 0 = 0 := by
  simp only [gaugePrimitivePolynomial, Polynomial.eval_mul, deviationPolynomial_zero, mul_zero]

theorem errorPrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (errorPrimitivePolynomial grade) :=
  (((deviationPolynomial_nonnegative (rotatedRecipePolynomial_nonnegative grade planarFrameColumns
    (rotatedPrimitivePolynomial_nonnegative grade) (frameInversePrimitivePolynomial_nonnegative grade))).add
    (deviationPolynomial_nonnegative (fluxRecipePolynomial_nonnegative grade (framePrimitivePolynomial_nonnegative grade)
      (frameInversePrimitivePolynomial_nonnegative grade)))).add
    (deviationPolynomial_nonnegative (rotatedRecipePolynomial_nonnegative grade thirdFrameColumn
      (rotatedPrimitivePolynomial_nonnegative grade) (frameInversePrimitivePolynomial_nonnegative grade)))).add
    (deviationPolynomial_nonnegative (traceRecipePolynomial_nonnegative grade (seedInversePrimitivePolynomial_nonnegative grade)
      (frameInversePrimitivePolynomial_nonnegative grade)))

theorem errorPrimitivePolynomial_zero (grade : ℕ) : (errorPrimitivePolynomial grade).eval 0 = 0 := by
  simp only [errorPrimitivePolynomial, Polynomial.eval_add, deviationPolynomial_zero, zero_add]

theorem physicalGaugeSize_primitive {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3)
    (frameSmall : ‖frameInverseInput parameters admissible epsilon base 0‖ ≤ 1 / 4)
    (grade high : ℕ) (ordered : grade ≤ high) :
    gaugeEpsilon ((physicalLedgerData parameters admissible rho alpha delta parameter epsilon base).gaugeDeviation grade) ≤
      (gaugePrimitivePolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) := by
  have seed := seedMatrixFamily_control parameters admissible rho alpha delta parameter epsilon base grade high ordered
  have derivative := seedDerivative_control parameters admissible rho alpha delta parameter epsilon base grade high ordered
  have inverse := actualFrameInverse_control parameters admissible rho alpha delta parameter epsilon base frameSmall grade high ordered
  have control := gaugeFamily_control admissible
    (derivative := fun q => seedDerivativeCoefficient admissible q rho alpha delta parameter)
    (referenceDerivative := zeroFamily L parameters.sigma0 parameters.gamma ell 2 2)
    seed derivative inverse
  have normBound : ‖(physicalLedgerData parameters admissible rho alpha delta parameter epsilon base).gaugeDeviation grade‖ ≤
      (deviationPolynomial (gaugeRecipePolynomial grade (seedPrimitivePolynomial grade)
        (primitiveLinearPolynomial grade) (frameInversePrimitivePolynomial grade))).eval
        (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) :=
    control.deviationBound.trans_eq (deviationPolynomial_eval _ _).symm
  exact (gaugeEpsilon_le_four_norm _).trans ((mul_le_mul_of_nonneg_left normBound (by norm_num)).trans_eq
    (by simp only [gaugePrimitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C]))

theorem physicalErrorSize_primitive {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3)
    (frameSmall : ‖frameInverseInput parameters admissible epsilon base 0‖ ≤ 1 / 4)
    (seedSmall : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade high : ℕ) (ordered : grade + 1 ≤ high) :
    errorCoefficientSize (physicalLedgerData parameters admissible rho alpha delta parameter epsilon base) grade ≤
      (errorPrimitivePolynomial grade).eval (primitiveSize parameters admissible rho alpha delta parameter epsilon base high) := by
  have frame := fullFrameFamily_control parameters admissible rho alpha delta parameter epsilon base grade high (by omega)
  have inverse := actualFrameInverse_control parameters admissible rho alpha delta parameter epsilon base frameSmall grade high (by omega)
  have seedInverse := actualSeedInverse_control parameters admissible rho alpha delta parameter epsilon base seedSmall grade high (by omega)
  have rotated := actualRotatedFrame_control parameters admissible rho alpha delta parameter epsilon base grade high ordered
  have planar := (rotatedProductFamily_control admissible planarFrameColumns rotated inverse).deviationBound
  have flux := (fluxFamily_control admissible frame inverse).deviationBound
  have third := (rotatedProductFamily_control admissible thirdFrameColumn rotated inverse).deviationBound
  have trace := (traceFamily_control admissible seedInverse inverse).deviationBound
  exact (add_le_add (add_le_add (add_le_add planar flux) third) trace).trans_eq (by
    simp only [errorPrimitivePolynomial, Polynomial.eval_add, deviationPolynomial_eval])

end Grad.GaugeCoefficients.Physical.Compensated
