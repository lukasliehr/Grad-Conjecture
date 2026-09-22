import GC10Weights
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section

set_option maxHeartbeats 500000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Algebra

def continuousOperatorComposition {inputDimension middleDimension outputDimension : ℕ}
    (outer : ContinuousMap ClosedDisk (OperatorValue middleDimension outputDimension))
    (inner : ContinuousMap ClosedDisk (OperatorValue inputDimension middleDimension)) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := (outer point).comp (inner point)
  continuous_toFun := by
    let composition := (ContinuousLinearMap.compL ℂ (PhysicalValue inputDimension)
      (PhysicalValue middleDimension) (PhysicalValue outputDimension)).bilinearRestrictScalars ℝ
    exact composition.isBoundedBilinearMap.continuous.comp
      (outer.continuous.prodMk inner.continuous)

def scaleRatio (L sigma gamma ell : ℝ) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (point : ClosedDisk) : ℝ :=
  coefficientScale L sigma gamma ell grade (first + second) index point /
    (coefficientScale L sigma gamma ell grade first
      (lowerDerivativeIndex index split) point *
    coefficientScale L sigma gamma ell grade second
      (upperDerivativeIndex index split) point)

theorem scaleRatio_nonnegative (L sigma gamma ell : ℝ) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) (point : ClosedDisk) :
    0 ≤ scaleRatio L sigma gamma ell grade first second index split point := by
  exact div_nonneg (coefficientScale_pos _ _ _ _ _ _ _ _).le
    (mul_nonneg (coefficientScale_pos _ _ _ _ _ _ _ _).le
      (coefficientScale_pos _ _ _ _ _ _ _ _).le)

theorem scaleRatio_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) (point : ClosedDisk) :
    scaleRatio L sigma gamma ell grade first second index split point ≤
      (Real.sqrt 2) ^ grade := by
  apply (div_le_iff₀ (mul_pos
    (coefficientScale_pos L sigma gamma ell grade first
      (lowerDerivativeIndex index split) point)
    (coefficientScale_pos L sigma gamma ell grade second
      (upperDerivativeIndex index split) point))).2
  simpa only [mul_assoc] using
    coefficientScale_comp_bound admissible grade first second index split point

theorem continuous_scaleRatio (L sigma gamma ell : ℝ) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    Continuous (scaleRatio L sigma gamma ell grade first second index split) := by
  unfold scaleRatio
  apply Continuous.div
  · simpa only using continuous_coefficientScale L sigma gamma ell grade (first + second) index
  · exact (continuous_coefficientScale L sigma gamma ell grade first
      (lowerDerivativeIndex index split)).mul
        (continuous_coefficientScale L sigma gamma ell grade second
          (upperDerivativeIndex index split))
  · intro point
    exact (mul_pos
      (coefficientScale_pos L sigma gamma ell grade first
        (lowerDerivativeIndex index split) point)
      (coefficientScale_pos L sigma gamma ell grade second
        (upperDerivativeIndex index split) point)).ne'

def weightedCompositionTerm (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) (first : ℤ)
    (inner : WeightedAmbient grade inputDimension middleDimension) (second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point :=
    (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      (outer (first, lowerDerivativeIndex index split) point).comp
        (inner (second, upperDerivativeIndex index split) point)
  continuous_toFun := by
    have ratioContinuous : Continuous fun point : ClosedDisk =>
        (scaleRatio L sigma gamma ell grade first second index split point : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_scaleRatio L sigma gamma ell grade first second index split)
    exact ratioContinuous.smul
      (continuousOperatorComposition
        (outer (first, lowerDerivativeIndex index split))
        (inner (second, upperDerivativeIndex index split))).continuous

theorem weightedCompositionTerm_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) (first : ℤ)
    (inner : WeightedAmbient grade inputDimension middleDimension) (second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    ‖weightedCompositionTerm L sigma gamma ell grade outer first inner second index split‖ ≤
      (Real.sqrt 2) ^ grade *
        ‖outer (first, lowerDerivativeIndex index split)‖ *
        ‖inner (second, upperDerivativeIndex index split)‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro point
  change ‖(scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      (outer (first, lowerDerivativeIndex index split) point).comp
        (inner (second, upperDerivativeIndex index split) point)‖ ≤ _
  rw [norm_smul]
  have ratioNorm : ‖(scaleRatio L sigma gamma ell grade first second index split point : ℂ)‖ ≤
      (Real.sqrt 2) ^ grade := by
    simpa [Real.norm_eq_abs, abs_of_nonneg
      (scaleRatio_nonnegative L sigma gamma ell grade first second index split point)] using
        scaleRatio_le admissible grade first second index split point
  calc
    _ ≤ ‖(scaleRatio L sigma gamma ell grade first second index split point : ℂ)‖ *
        (‖outer (first, lowerDerivativeIndex index split) point‖ *
          ‖inner (second, upperDerivativeIndex index split) point‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (Real.sqrt 2) ^ grade *
        (‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (second, upperDerivativeIndex index split)‖) := by
      exact mul_le_mul ratioNorm
        (mul_le_mul
          ((outer (first, lowerDerivativeIndex index split)).norm_coe_le_norm point)
          ((inner (second, upperDerivativeIndex index split)).norm_coe_le_norm point)
          (norm_nonneg (inner (second, upperDerivativeIndex index split) point))
          (norm_nonneg (outer (first, lowerDerivativeIndex index split))))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (pow_nonneg (Real.sqrt_nonneg 2) _)
    _ = _ := by ring

end Grad.GaugeCoefficients.Algebra
