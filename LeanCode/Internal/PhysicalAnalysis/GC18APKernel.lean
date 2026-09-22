import GC18APRatio
import GC18APL2Action

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher

def apRatioDerivative (sigma gamma ell : ℝ) (rank : ℕ) (word : Fin rank → Fin 2)
    (input shift : ℤ) : C(ClosedDisk, ℝ) where
  toFun point := orderedDerivative rank word (weightRatio sigma gamma ell (input + shift) input) point.val
  continuous_toFun := by
    have tensorContinuous : Continuous (fun point : ClosedDisk =>
        iteratedFDeriv ℝ rank (weightRatio sigma gamma ell (input + shift) input) point.val) :=
      ((weightRatio_contDiff sigma gamma ell (input + shift) input).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))).comp continuous_subtype_val
    dsimp [orderedDerivative]
    fun_prop

theorem apRatioDerivative_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (word : Fin rank → Fin 2)
    (input shift : ℤ) (point : ClosedDisk) :
    |apRatioDerivative sigma gamma ell rank word input shift point| ≤
      apRatioConstant L sigma gamma rank * scaledCellWeight L ell shift ^ rank *
        scaledCellWeight L ell input ^ rank * originalEnvelope sigma gamma ell shift point.val :=
  (orderedDerivative_norm_le rank word _ point.val).trans (apRatio_derivative_bound admissible rank input shift point)

def apKernelScalar {grade : ℕ} (L sigma gamma ell : ℝ) (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficientIndex inputIndex : DerivativeIndex grade) (input shift : ℤ) : C(ClosedDisk, ℝ) where
  toFun point :=
    (scaledCellWeight L ell (input + shift) ^ (grade - (rank + derivativeOrder coefficientIndex + derivativeOrder inputIndex)) *
      apRatioDerivative sigma gamma ell rank word input shift point) /
      (coefficientScale L sigma gamma ell grade shift coefficientIndex point *
        scaledCellWeight L ell input ^ (grade - derivativeOrder inputIndex))
  continuous_toFun := by
    apply (continuous_const.mul (apRatioDerivative sigma gamma ell rank word input shift).continuous).div
      ((continuous_coefficientScale L sigma gamma ell grade shift coefficientIndex).mul continuous_const)
    intro point
    exact (mul_pos (coefficientScale_pos L sigma gamma ell grade shift coefficientIndex point)
      (pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _)).ne'

theorem apKernelScalar_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (rank : ℕ) (word : Fin rank → Fin 2) (coefficientIndex inputIndex : DerivativeIndex grade)
    (rankBound : rank + derivativeOrder coefficientIndex + derivativeOrder inputIndex ≤ grade)
    (input shift : ℤ) (point : ClosedDisk) :
    |apKernelScalar L sigma gamma ell rank word coefficientIndex inputIndex input shift point| ≤
      apRatioConstant L sigma gamma rank * (Real.sqrt 2) ^ grade := by
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have outputNonnegative := scaledCellWeight_nonnegative L ell (input + shift)
  have constantNonnegative := apRatioConstant_nonnegative admissible rank
  have envelopePositive : 0 < originalEnvelope sigma gamma ell shift point.val := Real.exp_pos _
  have scalePositive := coefficientScale_pos L sigma gamma ell grade shift coefficientIndex point
  have denominatorPositive : 0 < coefficientScale L sigma gamma ell grade shift coefficientIndex point *
      scaledCellWeight L ell input ^ (grade - derivativeOrder inputIndex) :=
    mul_pos scalePositive (pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _)
  dsimp only [apKernelScalar, ContinuousMap.coe_mk]
  rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg outputNonnegative _), abs_of_pos denominatorPositive]
  apply (div_le_iff₀ denominatorPositive).mpr
  calc
    _ ≤ scaledCellWeight L ell (input + shift) ^
        (grade - (rank + derivativeOrder coefficientIndex + derivativeOrder inputIndex)) *
        (apRatioConstant L sigma gamma rank * scaledCellWeight L ell shift ^ rank *
          scaledCellWeight L ell input ^ rank * originalEnvelope sigma gamma ell shift point.val) :=
      mul_le_mul_of_nonneg_left (apRatioDerivative_bound admissible rank word input shift point) (by positivity)
    _ = (apRatioConstant L sigma gamma rank * originalEnvelope sigma gamma ell shift point.val) *
        (scaledCellWeight L ell (input + shift) ^
          (grade - (rank + derivativeOrder coefficientIndex + derivativeOrder inputIndex)) *
          (scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ rank)) := by ring
    _ ≤ (apRatioConstant L sigma gamma rank * originalEnvelope sigma gamma ell shift point.val) *
        ((Real.sqrt 2) ^ grade * scaledCellWeight L ell shift ^ (grade - derivativeOrder coefficientIndex) *
          scaledCellWeight L ell input ^ (grade - derivativeOrder inputIndex)) :=
      mul_le_mul_of_nonneg_left (apFrequency_allocation L ell grade rank (derivativeOrder coefficientIndex)
        (derivativeOrder inputIndex) rankBound input shift) (by positivity)
    _ = _ := by unfold coefficientScale; ring

def apKernelCoefficient {grade inputDimension outputDimension : ℕ} (L sigma gamma ell : ℝ)
    (rank : ℕ) (word : Fin rank → Fin 2) (coefficientIndex inputIndex : DerivativeIndex grade)
    (input shift : ℤ) (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun point := (apKernelScalar L sigma gamma ell rank word coefficientIndex inputIndex input shift point : ℂ) • coefficient point
  continuous_toFun := (Complex.continuous_ofReal.comp
    (apKernelScalar L sigma gamma ell rank word coefficientIndex inputIndex input shift).continuous).smul coefficient.continuous

theorem apKernelCoefficient_norm_le {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ} (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficientIndex inputIndex : DerivativeIndex grade)
    (rankBound : rank + derivativeOrder coefficientIndex + derivativeOrder inputIndex ≤ grade)
    (input shift : ℤ) (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    ‖apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift coefficient‖ ≤
      (apRatioConstant L sigma gamma rank * (Real.sqrt 2) ^ grade) * ‖coefficient‖ := by
  have constantNonnegative := apRatioConstant_nonnegative admissible rank
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro point
  change ‖(_ : ℂ) • coefficient point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (apKernelScalar_bound admissible rank word coefficientIndex inputIndex rankBound input shift point)
    (ContinuousMap.norm_coe_le_norm coefficient point) (norm_nonneg _) (by positivity)

end Grad.GaugeCoefficients.Physical.RadialLedger
