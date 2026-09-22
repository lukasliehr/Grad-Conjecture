import GC10Core

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem weightedCompositionTerm_add_outer
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerFirst outerSecond : WeightedAmbient grade middleDimension outputDimension)
    (first : ℤ) (inner : WeightedAmbient grade inputDimension middleDimension)
    (second : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTerm L sigma gamma ell grade (outerFirst + outerSecond)
        first inner second index split =
      weightedCompositionTerm L sigma gamma ell grade outerFirst first inner second index split +
        weightedCompositionTerm L sigma gamma ell grade outerSecond first inner second index split := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      ((outerFirst (first, lowerDerivativeIndex index split) point +
        outerSecond (first, lowerDerivativeIndex index split) point)
        (inner (second, upperDerivativeIndex index split) point value)) =
    (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
        outerFirst (first, lowerDerivativeIndex index split) point
          (inner (second, upperDerivativeIndex index split) point value) +
      (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
        outerSecond (first, lowerDerivativeIndex index split) point
          (inner (second, upperDerivativeIndex index split) point value)
  simp only [add_apply, smul_add]

theorem weightedCompositionTerm_add_inner
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) (first : ℤ)
    (innerFirst innerSecond : WeightedAmbient grade inputDimension middleDimension)
    (second : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTerm L sigma gamma ell grade outer first
        (innerFirst + innerSecond) second index split =
      weightedCompositionTerm L sigma gamma ell grade outer first innerFirst second index split +
        weightedCompositionTerm L sigma gamma ell grade outer first innerSecond second index split := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      (outer (first, lowerDerivativeIndex index split) point
        ((innerFirst (second, upperDerivativeIndex index split) point +
          innerSecond (second, upperDerivativeIndex index split) point) value)) =
    (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
        outer (first, lowerDerivativeIndex index split) point
          (innerFirst (second, upperDerivativeIndex index split) point value) +
      (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
        outer (first, lowerDerivativeIndex index split) point
          (innerSecond (second, upperDerivativeIndex index split) point value)
  rw [add_apply, map_add, smul_add]

theorem weightedCompositionTerm_smul_outer
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (first : ℤ) (inner : WeightedAmbient grade inputDimension middleDimension)
    (second : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTerm L sigma gamma ell grade (scalar • outer)
        first inner second index split =
      scalar • weightedCompositionTerm L sigma gamma ell grade
        outer first inner second index split := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      ((scalar • outer (first, lowerDerivativeIndex index split) point)
        (inner (second, upperDerivativeIndex index split) point value)) =
    scalar • ((scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      outer (first, lowerDerivativeIndex index split) point
        (inner (second, upperDerivativeIndex index split) point value))
  simp only [smul_apply, smul_smul]
  rw [mul_comm]

theorem weightedCompositionTerm_smul_inner
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (first : ℤ) (inner : WeightedAmbient grade inputDimension middleDimension)
    (second : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTerm L sigma gamma ell grade outer first
        (scalar • inner) second index split =
      scalar • weightedCompositionTerm L sigma gamma ell grade
        outer first inner second index split := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      (outer (first, lowerDerivativeIndex index split) point
        ((scalar • inner (second, upperDerivativeIndex index split) point) value)) =
    scalar • ((scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      outer (first, lowerDerivativeIndex index split) point
        (inner (second, upperDerivativeIndex index split) point value))
  rw [smul_apply, map_smul]
  simp only [smul_smul]
  rw [mul_comm]

theorem weightedCompositionTermSum_add_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerFirst outerSecond : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension (outerFirst + outerSecond) inner cell index split =
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outerFirst inner cell index split +
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outerSecond inner cell index split := by
  unfold weightedCompositionTermSum
  have firstSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outerFirst first inner (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outerFirst inner cell index split
  have secondSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outerSecond first inner (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outerSecond inner cell index split
  simp_rw [weightedCompositionTerm_add_outer L sigma gamma ell grade
    outerFirst outerSecond]
  exact firstSummable.tsum_add secondSummable

theorem weightedCompositionTermSum_add_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (innerFirst innerSecond : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer (innerFirst + innerSecond) cell index split =
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer innerFirst cell index split +
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer innerSecond cell index split := by
  unfold weightedCompositionTermSum
  have firstSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first innerFirst (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outer innerFirst cell index split
  have secondSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first innerSecond (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outer innerSecond cell index split
  simp_rw [weightedCompositionTerm_add_inner L sigma gamma ell grade outer]
  exact firstSummable.tsum_add secondSummable

theorem weightedCompositionTermSum_smul_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension (scalar • outer) inner cell index split =
      scalar • weightedCompositionTermSum L sigma gamma ell grade inputDimension
        middleDimension outputDimension outer inner cell index split := by
  unfold weightedCompositionTermSum
  have termIdentity :
      (fun first : ℤ => weightedCompositionTerm L sigma gamma ell grade
        (scalar • outer) first inner (cell - first) index split) =
      fun first : ℤ => scalar • weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split := by
    funext first
    exact weightedCompositionTerm_smul_outer L sigma gamma ell grade scalar
      outer first inner (cell - first) index split
  rw [termIdentity]
  have termSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outer inner cell index split
  exact Summable.tsum_const_smul scalar termSummable

theorem weightedCompositionTermSum_smul_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer (scalar • inner) cell index split =
      scalar • weightedCompositionTermSum L sigma gamma ell grade inputDimension
        middleDimension outputDimension outer inner cell index split := by
  unfold weightedCompositionTermSum
  have termIdentity :
      (fun first : ℤ => weightedCompositionTerm L sigma gamma ell grade
        outer first (scalar • inner) (cell - first) index split) =
      fun first : ℤ => scalar • weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split := by
    funext first
    exact weightedCompositionTerm_smul_inner L sigma gamma ell grade scalar
      outer first inner (cell - first) index split
  rw [termIdentity]
  have termSummable : Summable (fun first : ℤ =>
      weightedCompositionTerm L sigma gamma ell grade
        outer first inner (cell - first) index split) :=
    weightedCompositionTerm_summable admissible grade
      outer inner cell index split
  exact Summable.tsum_const_smul scalar termSummable

theorem weightedCompositionCoordinate_add_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerFirst outerSecond : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    weightedCompositionCoordinate L sigma gamma ell grade
        (outerFirst + outerSecond) inner cell index =
      weightedCompositionCoordinate L sigma gamma ell grade outerFirst inner cell index +
        weightedCompositionCoordinate L sigma gamma ell grade outerSecond inner cell index := by
  unfold weightedCompositionCoordinate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro split _membership
  change (splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension (outerFirst + outerSecond) inner cell index split =
    (splitMultiplicity index split : ℂ) •
        weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
          outputDimension outerFirst inner cell index split +
      (splitMultiplicity index split : ℂ) •
        weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
          outputDimension outerSecond inner cell index split
  rw [weightedCompositionTermSum_add_outer admissible grade
    outerFirst outerSecond inner cell index split, smul_add]

theorem weightedCompositionCoordinate_add_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (innerFirst innerSecond : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    weightedCompositionCoordinate L sigma gamma ell grade
        outer (innerFirst + innerSecond) cell index =
      weightedCompositionCoordinate L sigma gamma ell grade outer innerFirst cell index +
        weightedCompositionCoordinate L sigma gamma ell grade outer innerSecond cell index := by
  unfold weightedCompositionCoordinate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro split _membership
  change (splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer (innerFirst + innerSecond) cell index split =
    (splitMultiplicity index split : ℂ) •
        weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
          outputDimension outer innerFirst cell index split +
      (splitMultiplicity index split : ℂ) •
        weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
          outputDimension outer innerSecond cell index split
  rw [weightedCompositionTermSum_add_inner admissible grade
    outer innerFirst innerSecond cell index split, smul_add]

theorem weightedCompositionCoordinate_smul_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    weightedCompositionCoordinate L sigma gamma ell grade
        (scalar • outer) inner cell index =
      scalar • weightedCompositionCoordinate L sigma gamma ell grade outer inner cell index := by
  unfold weightedCompositionCoordinate
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  change (splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension (scalar • outer) inner cell index split =
    scalar • ((splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer inner cell index split)
  rw [weightedCompositionTermSum_smul_outer admissible grade
    scalar outer inner cell index split]
  simp only [smul_smul]
  rw [mul_comm]

theorem weightedCompositionCoordinate_smul_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    weightedCompositionCoordinate L sigma gamma ell grade
        outer (scalar • inner) cell index =
      scalar • weightedCompositionCoordinate L sigma gamma ell grade outer inner cell index := by
  unfold weightedCompositionCoordinate
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  change (splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer (scalar • inner) cell index split =
    scalar • ((splitMultiplicity index split : ℂ) •
      weightedCompositionTermSum L sigma gamma ell grade inputDimension middleDimension
        outputDimension outer inner cell index split)
  rw [weightedCompositionTermSum_smul_inner admissible grade
    scalar outer inner cell index split]
  simp only [smul_smul]
  rw [mul_comm]

theorem rawComposition_add_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerFirst outerSecond : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    rawComposition admissible grade (outerFirst + outerSecond) inner =
      rawComposition admissible grade outerFirst inner +
        rawComposition admissible grade outerSecond inner := by
  apply Subtype.ext
  funext pair
  exact weightedCompositionCoordinate_add_outer admissible grade
    outerFirst outerSecond inner pair.1 pair.2

theorem rawComposition_add_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (innerFirst innerSecond : WeightedAmbient grade inputDimension middleDimension) :
    rawComposition admissible grade outer (innerFirst + innerSecond) =
      rawComposition admissible grade outer innerFirst +
        rawComposition admissible grade outer innerSecond := by
  apply Subtype.ext
  funext pair
  exact weightedCompositionCoordinate_add_inner admissible grade
    outer innerFirst innerSecond pair.1 pair.2

theorem rawComposition_smul_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    rawComposition admissible grade (scalar • outer) inner =
      scalar • rawComposition admissible grade outer inner := by
  apply Subtype.ext
  funext pair
  exact weightedCompositionCoordinate_smul_outer admissible grade scalar
    outer inner pair.1 pair.2

theorem rawComposition_smul_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (scalar : ℂ) (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    rawComposition admissible grade outer (scalar • inner) =
      scalar • rawComposition admissible grade outer inner := by
  apply Subtype.ext
  funext pair
  exact weightedCompositionCoordinate_smul_inner admissible grade scalar
    outer inner pair.1 pair.2

end Grad.GaugeCoefficients.Algebra
