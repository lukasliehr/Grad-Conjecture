import AKAA2SharpActualPhaseJets
import GQC8ActualSmoothCoefficient

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher

/-- The genuine coefficient derivative times the genuine phase-ratio
 derivative, with exactly the input-cell payment allowed by ER17. -/
def startupAllocatedCoefficient {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (input shift : ℤ) : C(ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun point :=
    ((apRatioDerivative sigma gamma ell rank word input shift point /
      scaledCellWeight L ell input ^ (rank - 1) : ℝ) : ℂ) •
        coefficientDerivative coefficient shift index point
  continuous_toFun := (Complex.continuous_ofReal.comp
    ((apRatioDerivative sigma gamma ell rank word input shift).continuous.div_const _)).smul
      (coefficientDerivative coefficient shift index).continuous

theorem coefficientDerivative_scaled_norm {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (shift : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade shift index point *
      ‖coefficientDerivative coefficient shift index point‖ ≤
        ‖weightedDerivative coefficient shift index‖ := by
  calc
    _ = ‖(coefficientScale L sigma gamma ell grade shift index point : ℂ) •
        coefficientDerivative coefficient shift index point‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg
        (coefficientScale_pos L sigma gamma ell grade shift index point).le]
    _ = ‖weightedDerivative coefficient shift index point‖ := by
      rw [weighted_derivative_literal]
    _ ≤ _ := ContinuousMap.norm_coe_le_norm _ point

theorem startupAllocatedCoefficient_point_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocation : rank + derivativeOrder index ≤ grade)
    (input shift : ℤ) (point : ClosedDisk) :
    ‖startupAllocatedCoefficient coefficient rank word index input shift point‖ ≤
      apRatioConstant L sigma gamma rank * ‖weightedDerivative coefficient shift index‖ := by
  have inputPositive : 0 < scaledCellWeight L ell input ^ (rank - 1) :=
    pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _
  have constantNonnegative := apRatioConstant_nonnegative admissible rank
  have phaseBound := (orderedDerivative_norm_le rank word _ point.val).trans
    (startupRatio_derivative_bound admissible rank input shift point)
  have normalized : |apRatioDerivative sigma gamma ell rank word input shift point /
      scaledCellWeight L ell input ^ (rank - 1)| ≤
      apRatioConstant L sigma gamma rank * scaledCellWeight L ell shift ^ rank *
        originalEnvelope sigma gamma ell shift point.val := by
    rw [abs_div, abs_of_pos inputPositive]
    apply (div_le_iff₀ inputPositive).mpr
    exact phaseBound.trans_eq (by ring)
  have frequencyBound : scaledCellWeight L ell shift ^ rank ≤
      scaledCellWeight L ell shift ^ (grade - derivativeOrder index) :=
    pow_le_pow_right₀ (scaledCellWeight_one_le L ell shift) (by omega)
  have scalarBound : apRatioConstant L sigma gamma rank *
      scaledCellWeight L ell shift ^ rank * originalEnvelope sigma gamma ell shift point.val ≤
      apRatioConstant L sigma gamma rank * coefficientScale L sigma gamma ell grade shift index point := by
    unfold coefficientScale
    have envelopePositive : 0 < originalEnvelope sigma gamma ell shift point.val := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left frequencyBound
      (mul_nonneg constantNonnegative envelopePositive.le)]
  change ‖((_ : ℝ) : ℂ) • coefficientDerivative coefficient shift index point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (apRatioConstant L sigma gamma rank * coefficientScale L sigma gamma ell grade shift index point) *
        ‖coefficientDerivative coefficient shift index point‖ :=
      mul_le_mul_of_nonneg_right (normalized.trans scalarBound) (norm_nonneg _)
    _ = apRatioConstant L sigma gamma rank *
        (coefficientScale L sigma gamma ell grade shift index point *
          ‖coefficientDerivative coefficient shift index point‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (coefficientDerivative_scaled_norm coefficient shift index point) constantNonnegative

theorem startupAllocatedCoefficient_norm_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocation : rank + derivativeOrder index ≤ grade) (input shift : ℤ) :
    ‖startupAllocatedCoefficient coefficient rank word index input shift‖ ≤
      apRatioConstant L sigma gamma rank * ‖weightedDerivative coefficient shift index‖ :=
  (ContinuousMap.norm_le (startupAllocatedCoefficient coefficient rank word index input shift)
    (mul_nonneg (apRatioConstant_nonnegative admissible rank)
      (norm_nonneg (weightedDerivative coefficient shift index)))).mpr
    (startupAllocatedCoefficient_point_bound admissible coefficient rank word index allocation input shift)

end Grad.GaugeCoefficients.Physical.RadialLedger
