import QuotientTermBounds

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

theorem oneHighArgumentSum_pair (grade : ℕ) (arguments : Fin 2 → QuotientState parameters) :
    oneHighArgumentSum grade arguments =
      stateNorm (grade + 6) (arguments 0) * stateNorm 4 (arguments 1) +
        stateNorm (grade + 6) (arguments 1) * stateNorm 4 (arguments 0) := by
  have eraseZero : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have eraseOne : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  unfold oneHighArgumentSum
  rw [Fin.sum_univ_two, eraseZero, eraseOne, Finset.prod_singleton, Finset.prod_singleton]

theorem quotientDegreeZeroPart_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments : Fin 0 → QuotientState parameters,
        rowsGradeNorm grade (quotientDegreeZeroPart parameters arguments) ≤ constant := by
  refine ⟨originalGradeNorm grade (izConstantCore parameters) +
    originalGradeNorm grade (negIStarZConstantCore parameters),
    add_nonneg (originalGradeNorm_nonnegative _ _) (originalGradeNorm_nonnegative _ _), ?_⟩
  intro arguments
  have valueForm : quotientDegreeZeroPart parameters arguments =
      Pi.single 0 (izConstantCore parameters) +
        Pi.single 1 (negIStarZConstantCore parameters) := rfl
  rw [valueForm]
  apply (rowsGradeNorm_add_le grade _ _).trans
  rw [rowsGradeNorm_single, rowsGradeNorm_single]

theorem quotientDegreeOnePart_bound (cellLength : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments : Fin 1 → QuotientState parameters,
        rowsGradeNorm grade (quotientDegreeOnePart parameters cellLength arguments) ≤
          constant * oneHighArgumentSum grade arguments := by
  refine ⟨|2 * partialGradeConstant grade + 2 * partialGradeConstant grade +
    ((1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
      ‖physicalDotProduct‖ * (vectorDerivativeGradeConstant (grade + 3) *
        (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
      |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
        vectorDerivativeGradeConstant 3)) +
      (1 + orthogonalGradeConstant grade))|, abs_nonneg _, ?_⟩
  intro arguments
  have valueForm : quotientDegreeOnePart parameters cellLength arguments =
      Pi.single 0 (partialPlusCore parameters (statePotential (arguments 0))) +
        Pi.single 1 (partialMinusCore parameters (statePotential (arguments 0))) +
          Pi.single 3 (removeAngularCore parameters (actualMultilinearProduct parameters
              physicalDotProduct ![rotationCore parameters (stateField (arguments 0)),
                (cellLength : ℂ) • eTConstantCore parameters]) -
            removeAngularCore parameters
              (timeDerivativeCore parameters (statePotential (arguments 0)))) := rfl
  rw [valueForm, oneHighArgumentSum_single]
  set highNorm := stateNorm (grade + 6) (arguments 0) with highNormDef
  have highNonneg : 0 ≤ highNorm := stateNorm_nonneg _ _
  have plusBound : originalGradeNorm grade
      (partialPlusCore parameters (statePotential (arguments 0))) ≤
      2 * partialGradeConstant grade * highNorm :=
    (partialPlusCore_bound _ grade).trans (mul_le_mul_of_nonneg_left
      ((originalGradeNorm_statePotential_le (grade + 1) (arguments 0)).trans
        (stateNorm_mono (by omega) _))
      (mul_nonneg (by norm_num) (partialGradeConstant_nonnegative _)))
  have minusBound : originalGradeNorm grade
      (partialMinusCore parameters (statePotential (arguments 0))) ≤
      2 * partialGradeConstant grade * highNorm :=
    (partialMinusCore_bound _ grade).trans (mul_le_mul_of_nonneg_left
      ((originalGradeNorm_statePotential_le (grade + 1) (arguments 0)).trans
        (stateNorm_mono (by omega) _))
      (mul_nonneg (by norm_num) (partialGradeConstant_nonnegative _)))
  have timeBound : originalGradeNorm grade (removeAngularCore parameters
      (timeDerivativeCore parameters (statePotential (arguments 0)))) ≤
      (1 + orthogonalGradeConstant grade) * highNorm := by
    apply (removeAngularCore_bound _ grade).trans
    apply mul_le_mul_of_nonneg_left _ (by
      have orth := orthogonalGradeConstant_nonnegative grade
      linarith)
    exact (timeDerivativeCore_bound parameters grade _).trans
      ((originalGradeNorm_statePotential_le (grade + 1) (arguments 0)).trans
        (stateNorm_mono (by omega) _))
  have dotBound : originalGradeNorm grade (removeAngularCore parameters
      (actualMultilinearProduct parameters physicalDotProduct
        ![rotationCore parameters (stateField (arguments 0)),
          (cellLength : ℂ) • eTConstantCore parameters])) ≤
      (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
        ‖physicalDotProduct‖ * (vectorDerivativeGradeConstant (grade + 3) *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
          vectorDerivativeGradeConstant 3)) * highNorm := by
    have orthNonneg : (0 : ℝ) ≤ 1 + orthogonalGradeConstant grade := by
      have orth := orthogonalGradeConstant_nonnegative grade
      linarith
    have scaledLow : originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters) =
        |cellLength| * originalGradeNorm 3 (eTConstantCore parameters) := by
      rw [originalGradeNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have scaledHigh : originalGradeNorm (grade + 3)
        ((cellLength : ℂ) • eTConstantCore parameters) =
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) := by
      rw [originalGradeNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have rotHigh : originalGradeNorm (grade + 3)
        (rotationCore parameters (stateField (arguments 0))) ≤
        vectorDerivativeGradeConstant (grade + 3) * highNorm :=
      (rotationCore_bound parameters _ (grade + 3)).trans (mul_le_mul_of_nonneg_left
        ((originalGradeNorm_stateField_le (grade + 4) (arguments 0)).trans
          (stateNorm_mono (by omega) _)) (vectorDerivativeGradeConstant_nonnegative _))
    have rotLow : originalGradeNorm 3
        (rotationCore parameters (stateField (arguments 0))) ≤
        vectorDerivativeGradeConstant 3 * highNorm :=
      (rotationCore_bound parameters _ 3).trans (mul_le_mul_of_nonneg_left
        ((originalGradeNorm_stateField_le 4 (arguments 0)).trans
          (stateNorm_mono (by omega) _)) (vectorDerivativeGradeConstant_nonnegative _))
    have firstPiece : originalGradeNorm (grade + 3)
        (rotationCore parameters (stateField (arguments 0))) *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) ≤
        vectorDerivativeGradeConstant (grade + 3) *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) * highNorm := by
      have step := mul_le_mul_of_nonneg_right rotHigh
        (mul_nonneg (abs_nonneg cellLength)
          (originalGradeNorm_nonnegative 3 (eTConstantCore parameters)))
      apply step.trans_eq
      ring
    have secondPiece : |cellLength| * originalGradeNorm (grade + 3)
        (eTConstantCore parameters) * originalGradeNorm 3
          (rotationCore parameters (stateField (arguments 0))) ≤
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
          vectorDerivativeGradeConstant 3 * highNorm := by
      have step := mul_le_mul_of_nonneg_left rotLow
        (mul_nonneg (abs_nonneg cellLength)
          (originalGradeNorm_nonnegative (grade + 3) (eTConstantCore parameters)))
      apply step.trans_eq
      ring
    have inner : originalGradeNorm (grade + 3)
        (rotationCore parameters (stateField (arguments 0))) *
          originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters) +
        originalGradeNorm (grade + 3) ((cellLength : ℂ) • eTConstantCore parameters) *
          originalGradeNorm 3 (rotationCore parameters (stateField (arguments 0))) ≤
        (vectorDerivativeGradeConstant (grade + 3) *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
          vectorDerivativeGradeConstant 3) * highNorm := by
      rw [scaledLow, scaledHigh]
      exact (add_le_add firstPiece secondPiece).trans_eq (by ring)
    have productPiece : originalGradeNorm grade (actualMultilinearProduct parameters
        physicalDotProduct ![rotationCore parameters (stateField (arguments 0)),
          (cellLength : ℂ) • eTConstantCore parameters]) ≤
        productGradeConstant 1 grade * ‖physicalDotProduct‖ *
          (vectorDerivativeGradeConstant (grade + 3) *
            (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
          |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
            vectorDerivativeGradeConstant 3) * highNorm := by
      apply (actualMultilinearProduct_bound parameters physicalDotProduct _ grade).trans
      rw [oneHighExpression_pair]
      calc productGradeConstant 1 grade * ‖physicalDotProduct‖ *
            (originalGradeNorm (grade + 3)
              (rotationCore parameters (stateField (arguments 0))) *
              originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters) +
            originalGradeNorm (grade + 3) ((cellLength : ℂ) • eTConstantCore parameters) *
              originalGradeNorm 3 (rotationCore parameters (stateField (arguments 0)))) ≤
          productGradeConstant 1 grade * ‖physicalDotProduct‖ *
            ((vectorDerivativeGradeConstant (grade + 3) *
              (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
            |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
              vectorDerivativeGradeConstant 3) * highNorm) :=
            mul_le_mul_of_nonneg_left inner
              (mul_nonneg (productGradeConstant_nonnegative _ _) (norm_nonneg _))
        _ = _ := by ring
    apply (removeAngularCore_bound _ grade).trans
    calc (1 + orthogonalGradeConstant grade) * originalGradeNorm grade
          (actualMultilinearProduct parameters physicalDotProduct
            ![rotationCore parameters (stateField (arguments 0)),
              (cellLength : ℂ) • eTConstantCore parameters]) ≤
        (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
          ‖physicalDotProduct‖ * (vectorDerivativeGradeConstant (grade + 3) *
            (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
          |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
            vectorDerivativeGradeConstant 3) * highNorm) :=
          mul_le_mul_of_nonneg_left productPiece orthNonneg
      _ = _ := by ring
  have expand : rowsGradeNorm grade
      (Pi.single 0 (partialPlusCore parameters (statePotential (arguments 0))) +
        Pi.single 1 (partialMinusCore parameters (statePotential (arguments 0))) +
          Pi.single 3 (removeAngularCore parameters (actualMultilinearProduct parameters
              physicalDotProduct ![rotationCore parameters (stateField (arguments 0)),
                (cellLength : ℂ) • eTConstantCore parameters]) -
            removeAngularCore parameters
              (timeDerivativeCore parameters (statePotential (arguments 0))))) ≤
      originalGradeNorm grade (partialPlusCore parameters (statePotential (arguments 0))) +
        originalGradeNorm grade (partialMinusCore parameters (statePotential (arguments 0))) +
          (originalGradeNorm grade (removeAngularCore parameters
              (actualMultilinearProduct parameters physicalDotProduct
                ![rotationCore parameters (stateField (arguments 0)),
                  (cellLength : ℂ) • eTConstantCore parameters])) +
            originalGradeNorm grade (removeAngularCore parameters
              (timeDerivativeCore parameters (statePotential (arguments 0))))) := by
    apply (rowsGradeNorm_add_le grade _ _).trans
    apply add_le_add
    · apply (rowsGradeNorm_add_le grade _ _).trans
      rw [rowsGradeNorm_single, rowsGradeNorm_single]
    · rw [rowsGradeNorm_single]
      exact originalGradeNorm_sub_le grade _ _
  apply expand.trans
  have collected : originalGradeNorm grade
        (partialPlusCore parameters (statePotential (arguments 0))) +
      originalGradeNorm grade (partialMinusCore parameters (statePotential (arguments 0))) +
        (originalGradeNorm grade (removeAngularCore parameters
            (actualMultilinearProduct parameters physicalDotProduct
              ![rotationCore parameters (stateField (arguments 0)),
                (cellLength : ℂ) • eTConstantCore parameters])) +
          originalGradeNorm grade (removeAngularCore parameters
            (timeDerivativeCore parameters (statePotential (arguments 0))))) ≤
      (2 * partialGradeConstant grade + 2 * partialGradeConstant grade +
        ((1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
          ‖physicalDotProduct‖ * (vectorDerivativeGradeConstant (grade + 3) *
            (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters)) +
          |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
            vectorDerivativeGradeConstant 3)) +
          (1 + orthogonalGradeConstant grade))) * highNorm := by
    have summed := add_le_add (add_le_add plusBound minusBound)
      (add_le_add dotBound timeBound)
    apply summed.trans_eq
    ring
  apply collected.trans
  exact mul_le_mul_of_nonneg_right (le_abs_self _) highNonneg

end Grad.NonlinearQuotientBounds
