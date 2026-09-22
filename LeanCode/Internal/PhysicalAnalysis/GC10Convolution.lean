import GC10Terms

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

/-- `(output, first) ↦ (first, output-first)` is the cell reindexing behind
the full convolution. -/
def cellConvolutionEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun pair := (pair.2, pair.1 - pair.2)
  invFun pair := (pair.1 + pair.2, pair.1)
  left_inv pair := by ext <;> simp
  right_inv pair := by ext <;> simp

theorem ambient_norm_formula
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖coefficient‖ = ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
      ‖coefficient (cell, index)‖ := by
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [lp.norm_eq_tsum_rpow (by norm_num), oneToReal]
  simp only [Real.rpow_one]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one]
  have summable : Summable
      (fun pair : ℤ × DerivativeIndex grade => ‖coefficient pair‖) := by
    simpa only [oneToReal, Real.rpow_one] using
      (lp.memℓp coefficient).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  calc
    (∑' pair : ℤ × DerivativeIndex grade, ‖coefficient pair‖) =
        ∑' cell : ℤ, ∑' index : DerivativeIndex grade,
          ‖coefficient (cell, index)‖ := summable.tsum_prod
    _ = ∑' index : DerivativeIndex grade, ∑' cell : ℤ,
          ‖coefficient (cell, index)‖ := by
      exact (show Summable (Function.uncurry (fun cell : ℤ =>
          fun index : DerivativeIndex grade => ‖coefficient (cell, index)‖)) from by
            change Summable (fun pair : ℤ × DerivativeIndex grade => ‖coefficient pair‖)
            exact summable).tsum_comm.symm
    _ = _ := by simp only [tsum_fintype]

theorem coordinate_norm_summable
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    Summable (fun cell : ℤ => ‖coefficient (cell, index)‖) := by
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  have all : Summable (fun pair : ℤ × DerivativeIndex grade => ‖coefficient pair‖) := by
    simpa only [oneToReal, Real.rpow_one] using
      (lp.memℓp coefficient).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  exact all.prod_symm.prod_factor index

theorem coordinate_norm_sum_le
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    ∑' cell : ℤ, ‖coefficient (cell, index)‖ ≤ ‖coefficient‖ := by
  rw [ambient_norm_formula coefficient]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun other : DerivativeIndex grade => ∑' cell : ℤ, ‖coefficient (cell, other)‖)
    (fun other _ => tsum_nonneg fun cell => norm_nonneg (coefficient (cell, other)))
    (Finset.mem_univ index)

theorem convolution_norm_pair_summable
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (outerIndex innerIndex : DerivativeIndex grade) :
    Summable (fun pair : ℤ × ℤ =>
      ‖outer (pair.1, outerIndex)‖ * ‖inner (pair.2, innerIndex)‖) :=
  (coordinate_norm_summable outer outerIndex).mul_of_nonneg
    (coordinate_norm_summable inner innerIndex)
    (fun cell => norm_nonneg (outer (cell, outerIndex)))
    (fun cell => norm_nonneg (inner (cell, innerIndex)))

theorem convolution_norm_reindexed_summable
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (outerIndex innerIndex : DerivativeIndex grade) :
    Summable (fun pair : ℤ × ℤ =>
      ‖outer (pair.2, outerIndex)‖ * ‖inner (pair.1 - pair.2, innerIndex)‖) := by
  exact cellConvolutionEquiv.summable_iff.mpr
    (convolution_norm_pair_summable outer inner outerIndex innerIndex)

theorem convolution_norm_total_le
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (outerIndex innerIndex : DerivativeIndex grade) :
    (∑' cell : ℤ, ∑' first : ℤ,
      ‖outer (first, outerIndex)‖ * ‖inner (cell - first, innerIndex)‖) ≤
        ‖outer‖ * ‖inner‖ := by
  have pairSummable := convolution_norm_pair_summable outer inner outerIndex innerIndex
  have reindexed := convolution_norm_reindexed_summable outer inner outerIndex innerIndex
  calc
    (∑' cell : ℤ, ∑' first : ℤ,
        ‖outer (first, outerIndex)‖ * ‖inner (cell - first, innerIndex)‖) =
      ∑' pair : ℤ × ℤ,
        ‖outer (pair.2, outerIndex)‖ * ‖inner (pair.1 - pair.2, innerIndex)‖ :=
      reindexed.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ,
        ‖outer (pair.1, outerIndex)‖ * ‖inner (pair.2, innerIndex)‖ :=
      cellConvolutionEquiv.tsum_eq (fun pair : ℤ × ℤ =>
        ‖outer (pair.1, outerIndex)‖ * ‖inner (pair.2, innerIndex)‖)
    _ = (∑' first : ℤ, ‖outer (first, outerIndex)‖) *
        (∑' second : ℤ, ‖inner (second, innerIndex)‖) :=
      ((coordinate_norm_summable outer outerIndex).tsum_mul_tsum
        (coordinate_norm_summable inner innerIndex) pairSummable).symm
    _ ≤ ‖outer‖ * ‖inner‖ :=
      mul_le_mul (coordinate_norm_sum_le outer outerIndex)
        (coordinate_norm_sum_le inner innerIndex)
        (tsum_nonneg fun cell => norm_nonneg (inner (cell, innerIndex)))
        (norm_nonneg outer)

def weightedCompositionCoordinate (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  ∑ split : DerivativeSplit index,
    (splitMultiplicity index split : ℂ) •
      ∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split

def weightedCompositionMajorant (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) : ℝ :=
  (Real.sqrt 2) ^ grade *
    ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
      ∑' first : ℤ,
        ‖outer (first, lowerDerivativeIndex index split)‖ *
          ‖inner (cell - first, upperDerivativeIndex index split)‖

end Grad.GaugeCoefficients.Algebra
