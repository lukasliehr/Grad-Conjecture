import GC10Smooth

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem weightedSingle_apply (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell other : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    weightedSingle L sigma gamma ell grade cell field (other, index) =
      if other = cell then
        weightedSmoothDerivative L sigma gamma ell grade cell field index else 0 := by
  classical
  unfold weightedSingle
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  by_cases same : other = cell
  · subst other
    simp only [Pi.single_apply]
    simp
  · simp [same]

theorem weightedSingle_apply_same (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    weightedSingle L sigma gamma ell grade cell field (cell, index) =
      weightedSmoothDerivative L sigma gamma ell grade cell field index := by
  rw [weightedSingle_apply, if_pos rfl]

theorem weightedCompositionTerm_single_point {L sigma gamma ell : ℝ}
    (grade : ℕ) {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (point : ClosedDisk) :
    weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) outerCell
        (weightedSingle L sigma gamma ell grade innerCell inner) innerCell
        index split point =
      (coefficientScale L sigma gamma ell grade (outerCell + innerCell) index point : ℂ) •
        (smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex index split)) point).comp
        (smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex index split)) point) := by
  rw [show weightedCompositionTerm L sigma gamma ell grade
      (weightedSingle L sigma gamma ell grade outerCell outer) outerCell
      (weightedSingle L sigma gamma ell grade innerCell inner) innerCell
      index split point =
    (scaleRatio L sigma gamma ell grade outerCell innerCell index split point : ℂ) •
      ((weightedSingle L sigma gamma ell grade outerCell outer
        (outerCell, lowerDerivativeIndex index split)) point).comp
      ((weightedSingle L sigma gamma ell grade innerCell inner
        (innerCell, upperDerivativeIndex index split)) point)
    from rfl]
  rw [weightedSingle_apply_same, weightedSingle_apply_same]
  change (scaleRatio L sigma gamma ell grade outerCell innerCell index split point : ℂ) •
      (((coefficientScale L sigma gamma ell grade outerCell
          (lowerDerivativeIndex index split) point : ℂ) •
        smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex index split)) point).comp
      ((coefficientScale L sigma gamma ell grade innerCell
          (upperDerivativeIndex index split) point : ℂ) •
        smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex index split)) point)) = _
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  have outerNonzero :
      (coefficientScale L sigma gamma ell grade outerCell
        (lowerDerivativeIndex index split) point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade outerCell
        (lowerDerivativeIndex index split) point).ne'
  have innerNonzero :
      (coefficientScale L sigma gamma ell grade innerCell
        (upperDerivativeIndex index split) point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade innerCell
        (upperDerivativeIndex index split) point).ne'
  have scalarIdentity :
      (scaleRatio L sigma gamma ell grade outerCell innerCell index split point : ℂ) *
          (coefficientScale L sigma gamma ell grade outerCell
            (lowerDerivativeIndex index split) point : ℂ) *
          (coefficientScale L sigma gamma ell grade innerCell
            (upperDerivativeIndex index split) point : ℂ) =
        (coefficientScale L sigma gamma ell grade (outerCell + innerCell)
          index point : ℂ) := by
    unfold scaleRatio
    push_cast
    field_simp
  rw [map_smul]
  simp only [smul_smul]
  rw [← mul_assoc, scalarIdentity]

theorem weightedCompositionTerm_single_zero_of_first_ne {L sigma gamma ell : ℝ}
    (grade : ℕ) {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell first second : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (different : first ≠ outerCell) :
    weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) first
        (weightedSingle L sigma gamma ell grade innerCell inner) second
        index split = 0 := by
  apply ContinuousMap.ext
  intro point
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      ((weightedSingle L sigma gamma ell grade outerCell outer
        (first, lowerDerivativeIndex index split)) point).comp
      ((weightedSingle L sigma gamma ell grade innerCell inner
        (second, upperDerivativeIndex index split)) point) = 0
  rw [weightedSingle_apply (inputDimension := middleDimension)
    (outputDimension := outputDimension) L sigma gamma ell grade
    outerCell first outer (lowerDerivativeIndex index split)]
  simp only [if_neg different]
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
    (0 : OperatorValue inputDimension outputDimension) = 0
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
    (0 : PhysicalValue outputDimension) = 0
  exact smul_zero _

theorem weightedCompositionTermSum_single
    {L sigma gamma ell : ℝ} (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
      (weightedSingle L sigma gamma ell grade outerCell outer) first
      (weightedSingle L sigma gamma ell grade innerCell inner)
        (outerCell + innerCell - first) index split) =
      weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) outerCell
        (weightedSingle L sigma gamma ell grade innerCell inner) innerCell
        index split := by
  rw [tsum_eq_single outerCell]
  · congr 2
    omega
  · intro first different
    exact weightedCompositionTerm_single_zero_of_first_ne grade outerCell innerCell
      first (outerCell + innerCell - first) outer inner index split different

theorem weightedCompositionCoordinate_single
    {L sigma gamma ell : ℝ} (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) :
    weightedCompositionCoordinate L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer)
        (weightedSingle L sigma gamma ell grade innerCell inner)
        (outerCell + innerCell) index =
      weightedSmoothDerivative L sigma gamma ell grade (outerCell + innerCell)
        (smoothOperatorCompose outer inner) index := by
  apply ContinuousMap.ext
  intro point
  change (∑ split : DerivativeSplit index,
      (splitMultiplicity index split : ℂ) •
        (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
          (weightedSingle L sigma gamma ell grade outerCell outer) first
          (weightedSingle L sigma gamma ell grade innerCell inner)
            (outerCell + innerCell - first) index split)) point = _
  have evaluation :
      (∑ split : DerivativeSplit index,
        (splitMultiplicity index split : ℂ) •
          (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
            (weightedSingle L sigma gamma ell grade outerCell outer) first
            (weightedSingle L sigma gamma ell grade innerCell inner)
              (outerCell + innerCell - first) index split)) point =
      ∑ split : DerivativeSplit index,
        ((splitMultiplicity index split : ℂ) •
          (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
            (weightedSingle L sigma gamma ell grade outerCell outer) first
            (weightedSingle L sigma gamma ell grade innerCell inner)
              (outerCell + innerCell - first) index split)) point := by
    let evaluate :
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) →+
          OperatorValue inputDimension outputDimension := {
      toFun function := function point
      map_zero' := rfl
      map_add' _ _ := rfl }
    change evaluate (∑ split : DerivativeSplit index,
        (splitMultiplicity index split : ℂ) •
          (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
            (weightedSingle L sigma gamma ell grade outerCell outer) first
            (weightedSingle L sigma gamma ell grade innerCell inner)
              (outerCell + innerCell - first) index split)) = _
    rw [map_sum]
    rfl
  rw [evaluation]
  change (∑ split : DerivativeSplit index,
      ((splitMultiplicity index split : ℂ) •
        (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
          (weightedSingle L sigma gamma ell grade outerCell outer) first
          (weightedSingle L sigma gamma ell grade innerCell inner)
            (outerCell + innerCell - first) index split)) point) =
    (coefficientScale L sigma gamma ell grade (outerCell + innerCell) index point : ℂ) •
      smoothOperatorDerivative (smoothOperatorCompose outer inner)
        (derivativeMultiIndex index) point
  rw [smoothOperatorCompose_derivative]
  change (∑ split : DerivativeSplit index,
      ((splitMultiplicity index split : ℂ) •
        (∑' first : ℤ, weightedCompositionTerm L sigma gamma ell grade
          (weightedSingle L sigma gamma ell grade outerCell outer) first
          (weightedSingle L sigma gamma ell grade innerCell inner)
            (outerCell + innerCell - first) index split)) point) =
    (coefficientScale L sigma gamma ell grade (outerCell + innerCell) index point : ℂ) •
      (∑ split : DerivativeSplit index,
        (splitMultiplicity index split : ℂ) •
          continuousOperatorComposition
            (smoothOperatorDerivative outer
              (derivativeMultiIndex (lowerDerivativeIndex index split)))
            (smoothOperatorDerivative inner
              (derivativeMultiIndex (upperDerivativeIndex index split)))) point
  let scale : ℂ :=
    coefficientScale L sigma gamma ell grade (outerCell + innerCell) index point
  let pieces := fun split : DerivativeSplit index =>
    (splitMultiplicity index split : ℂ) •
      continuousOperatorComposition
        (smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex index split)))
        (smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex index split)))
  have piecesEvaluation :
      (∑ split : DerivativeSplit index, pieces split) point =
        ∑ split : DerivativeSplit index, pieces split point := by
    let evaluate :
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) →+
          OperatorValue inputDimension outputDimension := {
      toFun function := function point
      map_zero' := rfl
      map_add' _ _ := rfl }
    change evaluate (∑ split : DerivativeSplit index, pieces split) = _
    rw [map_sum]
    rfl
  rw [piecesEvaluation]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  rw [weightedCompositionTermSum_single grade outerCell innerCell outer inner index split]
  change (splitMultiplicity index split : ℂ) •
      weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) outerCell
        (weightedSingle L sigma gamma ell grade innerCell inner) innerCell
        index split point =
    scale • (pieces split point)
  rw [weightedCompositionTerm_single_point grade outerCell innerCell outer inner index split point]
  change (splitMultiplicity index split : ℂ) •
      (scale •
        (smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex index split)) point).comp
        (smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex index split)) point)) =
    scale • (pieces split point)
  have pieces_apply : pieces split point =
      (splitMultiplicity index split : ℂ) •
        (smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex index split)) point).comp
        (smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex index split)) point) := by
    let evaluate :
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) →ₗ[ℂ]
          OperatorValue inputDimension outputDimension := {
      toFun function := function point
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    change evaluate (pieces split) = _
    rw [show pieces split =
        (splitMultiplicity index split : ℂ) •
          continuousOperatorComposition
            (smoothOperatorDerivative outer
              (derivativeMultiIndex (lowerDerivativeIndex index split)))
            (smoothOperatorDerivative inner
              (derivativeMultiIndex (upperDerivativeIndex index split))) from rfl]
    rw [map_smul]
    rfl
  rw [pieces_apply]
  simp only [smul_smul]
  rw [mul_comm]

theorem weightedCompositionTerm_single_zero_of_second_ne {L sigma gamma ell : ℝ}
    (grade : ℕ) {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell first second : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (different : second ≠ innerCell) :
    weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) first
        (weightedSingle L sigma gamma ell grade innerCell inner) second
        index split = 0 := by
  apply ContinuousMap.ext
  intro point
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
      ((weightedSingle L sigma gamma ell grade outerCell outer
        (first, lowerDerivativeIndex index split)) point).comp
      ((weightedSingle L sigma gamma ell grade innerCell inner
        (second, upperDerivativeIndex index split)) point) = 0
  rw [weightedSingle_apply (inputDimension := inputDimension)
    (outputDimension := middleDimension) L sigma gamma ell grade
    innerCell second inner (upperDerivativeIndex index split)]
  simp only [if_neg different]
  rw [show (0 : ContinuousMap ClosedDisk
      (OperatorValue inputDimension middleDimension)) point = 0 from rfl,
    ContinuousLinearMap.comp_zero]
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
    (0 : OperatorValue inputDimension outputDimension) = 0
  apply ContinuousLinearMap.ext
  intro value
  change (scaleRatio L sigma gamma ell grade first second index split point : ℂ) •
    (0 : PhysicalValue outputDimension) = 0
  exact smul_zero _

theorem weightedCompositionTerm_single_zero_of_output_ne {L sigma gamma ell : ℝ}
    (grade : ℕ) {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell outputCell first : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index)
    (different : outputCell ≠ outerCell + innerCell) :
    weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) first
        (weightedSingle L sigma gamma ell grade innerCell inner) (outputCell - first)
        index split = 0 := by
  by_cases firstSame : first = outerCell
  · subst first
    apply weightedCompositionTerm_single_zero_of_second_ne grade
    intro secondSame
    apply different
    omega
  · exact weightedCompositionTerm_single_zero_of_first_ne grade outerCell innerCell
      first (outputCell - first) outer inner index split firstSame

theorem weightedCompositionCoordinate_single_zero_of_output_ne
    {L sigma gamma ell : ℝ} (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell outputCell : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : DerivativeIndex grade)
    (different : outputCell ≠ outerCell + innerCell) :
    weightedCompositionCoordinate L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer)
        (weightedSingle L sigma gamma ell grade innerCell inner)
        outputCell index = 0 := by
  unfold weightedCompositionCoordinate
  apply Finset.sum_eq_zero
  intro split _membership
  have termFunctionZero :
      (fun first : ℤ => weightedCompositionTerm L sigma gamma ell grade
        (weightedSingle L sigma gamma ell grade outerCell outer) first
        (weightedSingle L sigma gamma ell grade innerCell inner) (outputCell - first)
        index split) = 0 := by
    funext first
    exact weightedCompositionTerm_single_zero_of_output_ne grade outerCell innerCell
      outputCell first outer inner index split different
  rw [termFunctionZero]
  have zeroTsum :
      tsum (0 : ℤ → ContinuousMap ClosedDisk
        (OperatorValue inputDimension outputDimension)) = 0 := tsum_zero
  rw [zeroTsum]
  apply ContinuousMap.ext
  intro point
  change (splitMultiplicity index split : ℂ) •
    (0 : OperatorValue inputDimension outputDimension) = 0
  apply ContinuousLinearMap.ext
  intro value
  change (splitMultiplicity index split : ℂ) •
    (0 : PhysicalValue outputDimension) = 0
  exact smul_zero _

theorem rawComposition_weightedSingle {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outerCell innerCell : ℤ)
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension) :
    rawComposition admissible grade
        (weightedSingle L sigma gamma ell grade outerCell outer)
        (weightedSingle L sigma gamma ell grade innerCell inner) =
      weightedSingle L sigma gamma ell grade (outerCell + innerCell)
        (smoothOperatorCompose outer inner) := by
  apply Subtype.ext
  funext pair
  rcases pair with ⟨outputCell, index⟩
  change weightedCompositionCoordinate L sigma gamma ell grade
      (weightedSingle L sigma gamma ell grade outerCell outer)
      (weightedSingle L sigma gamma ell grade innerCell inner)
      outputCell index = _
  by_cases same : outputCell = outerCell + innerCell
  · subst outputCell
    rw [weightedCompositionCoordinate_single,
      weightedSingle_apply_same]
  · rw [weightedCompositionCoordinate_single_zero_of_output_ne
      grade outerCell innerCell outputCell outer inner index same]
    rw [weightedSingle_apply, if_neg same]

end Grad.GaugeCoefficients.Algebra
