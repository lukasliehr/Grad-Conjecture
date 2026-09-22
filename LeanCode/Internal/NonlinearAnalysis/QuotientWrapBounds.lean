import QuotientHighDegreeBounds

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

theorem quotientDegreeThreePart_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments : Fin 3 → QuotientState parameters,
        rowsGradeNorm grade (quotientDegreeThreePart parameters arguments) ≤
          constant * oneHighArgumentSum grade arguments := by
  have orthNonneg : (0 : ℝ) ≤ 1 + orthogonalGradeConstant grade := by
    have orth := orthogonalGradeConstant_nonnegative grade
    linarith
  have tripleFactorNonneg : (0 : ℝ) ≤ partialGradeConstant 3 +
      partialGradeConstant (grade + 3) + 1 := by
    have p3 := partialGradeConstant_nonnegative 3
    have pg := partialGradeConstant_nonnegative (grade + 3)
    linarith
  have wrapFactorNonneg : (0 : ℝ) ≤ vectorDerivativeGradeConstant 3 +
      vectorDerivativeGradeConstant (grade + 3) + ‖tangentGeneratorMap‖ := by
    have v3 := vectorDerivativeGradeConstant_nonnegative 3
    have vg := vectorDerivativeGradeConstant_nonnegative (grade + 3)
    have tg := norm_nonneg tangentGeneratorMap
    linarith
  have wrapNonneg : (0 : ℝ) ≤ (1 + orthogonalGradeConstant grade) *
      (productGradeConstant 1 grade * ‖physicalDotProduct‖) *
      (vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) +
        ‖tangentGeneratorMap‖) ^ 2 :=
    mul_nonneg (mul_nonneg orthNonneg (mul_nonneg (productGradeConstant_nonnegative _ _)
      (norm_nonneg _))) (pow_nonneg wrapFactorNonneg 2)
  refine ⟨|(1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
      ‖determinantMultilinear‖) * (partialGradeConstant 3 +
        partialGradeConstant (grade + 3) + 1) ^ 3 +
    (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
      ‖physicalDotProduct‖) * (vectorDerivativeGradeConstant 3 +
        vectorDerivativeGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 2|,
    abs_nonneg _, ?_⟩
  intro arguments
  have oneHighNonneg := oneHighArgumentSum_nonneg grade arguments
  have valueForm : quotientDegreeThreePart parameters arguments =
      Pi.single 2 (removeAngularCore parameters (actualMultilinearProduct parameters
          determinantMultilinear ![partialCore parameters 0 (stateField (arguments 0)),
            partialCore parameters 1 (stateField (arguments 1)),
            timeDerivativeCore parameters (stateField (arguments 2))])) +
      Pi.single 3 (stateScalar (arguments 0) • removeAngularCore parameters
        (actualMultilinearProduct parameters physicalDotProduct
          ![rotationCore parameters (stateField (arguments 1)),
            valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))])) := rfl
  have detLow : ∀ index, originalGradeNorm 3
      ((![partialCore parameters 0 (stateField (arguments 0)),
        partialCore parameters 1 (stateField (arguments 1)),
        timeDerivativeCore parameters (stateField (arguments 2))]) index) ≤
      (partialGradeConstant 3 + partialGradeConstant (grade + 3) + 1) *
        stateNorm 4 (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partial 0 (arguments 0) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
    · exact (factor_partial 1 (arguments 1) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
    · apply (factor_timeDerivative (arguments 2) 3).trans
      apply le_mul_of_one_le_left (stateNorm_nonneg 4 _)
      linarith [partialGradeConstant_nonnegative 3, partialGradeConstant_nonnegative (grade + 3)]
  have detHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![partialCore parameters 0 (stateField (arguments 0)),
        partialCore parameters 1 (stateField (arguments 1)),
        timeDerivativeCore parameters (stateField (arguments 2))]) index) ≤
      (partialGradeConstant 3 + partialGradeConstant (grade + 3) + 1) *
        stateNorm (grade + 4) (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partial 0 (arguments 0) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3]) (stateNorm_nonneg _ _))
    · exact (factor_partial 1 (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3]) (stateNorm_nonneg _ _))
    · apply (factor_timeDerivative (arguments 2) (grade + 3)).trans
      apply le_mul_of_one_le_left (stateNorm_nonneg _ _)
      linarith [partialGradeConstant_nonnegative 3, partialGradeConstant_nonnegative (grade + 3)]
  have detBound := triple_post_argument_bound grade (1 + orthogonalGradeConstant grade)
    (fun field => removeAngularCore_bound field grade) orthNonneg determinantMultilinear
    ![partialCore parameters 0 (stateField (arguments 0)),
      partialCore parameters 1 (stateField (arguments 1)),
      timeDerivativeCore parameters (stateField (arguments 2))] arguments _
    tripleFactorNonneg detLow detHigh
  have wrapLow : ∀ index, originalGradeNorm 3
      ((![rotationCore parameters (stateField (arguments 1)),
        valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))]) index) ≤
      (vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) +
        ‖tangentGeneratorMap‖) *
        stateNorm 4 ((fun position : Fin 2 => arguments position.succ) index) := by
    intro index
    fin_cases index
    · exact (factor_rotation (arguments 1) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [vectorDerivativeGradeConstant_nonnegative (grade + 3),
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg 4 _))
    · exact (factor_tangent (arguments 2) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
  have wrapHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![rotationCore parameters (stateField (arguments 1)),
        valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))]) index) ≤
      (vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) +
        ‖tangentGeneratorMap‖) *
        stateNorm (grade + 4) ((fun position : Fin 2 => arguments position.succ) index) := by
    intro index
    fin_cases index
    · exact (factor_rotation (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [vectorDerivativeGradeConstant_nonnegative 3,
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg _ _))
    · exact (factor_tangent (arguments 2) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg _ _))
  have wrapInner := pair_post_argument_bound grade (1 + orthogonalGradeConstant grade)
    (fun field => removeAngularCore_bound field grade) orthNonneg physicalDotProduct
    ![rotationCore parameters (stateField (arguments 1)),
      valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))]
    (fun position : Fin 2 => arguments position.succ) _ wrapFactorNonneg wrapLow wrapHigh
  have wrapBound : originalGradeNorm grade (stateScalar (arguments 0) •
      removeAngularCore parameters (actualMultilinearProduct parameters physicalDotProduct
        ![rotationCore parameters (stateField (arguments 1)),
          valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))])) ≤
      (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
        ‖physicalDotProduct‖) * (vectorDerivativeGradeConstant 3 +
          vectorDerivativeGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 2 *
        oneHighArgumentSum grade arguments := by
    rw [originalGradeNorm_smul]
    calc ‖stateScalar (arguments 0)‖ * originalGradeNorm grade
          (removeAngularCore parameters (actualMultilinearProduct parameters
            physicalDotProduct ![rotationCore parameters (stateField (arguments 1)),
              valueMapCore parameters tangentGeneratorMap (stateField (arguments 2))])) ≤
        ‖stateScalar (arguments 0)‖ * ((1 + orthogonalGradeConstant grade) *
          (productGradeConstant 1 grade * ‖physicalDotProduct‖) *
          (vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) +
            ‖tangentGeneratorMap‖) ^ 2 *
          oneHighArgumentSum grade (fun position : Fin 2 => arguments position.succ)) :=
          mul_le_mul_of_nonneg_left wrapInner (norm_nonneg _)
      _ = (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
          ‖physicalDotProduct‖) * (vectorDerivativeGradeConstant 3 +
            vectorDerivativeGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 2 *
          (‖stateScalar (arguments 0)‖ *
            oneHighArgumentSum grade (fun position : Fin 2 => arguments position.succ)) := by
          ring
      _ ≤ (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
          ‖physicalDotProduct‖) * (vectorDerivativeGradeConstant 3 +
            vectorDerivativeGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 2 *
          oneHighArgumentSum grade arguments :=
          mul_le_mul_of_nonneg_left (scalar_wrap_argument_bound grade arguments) wrapNonneg
  rw [valueForm]
  apply (rowsGradeNorm_two_singles grade 2 3 _ _).trans
  apply (add_le_add detBound wrapBound).trans
  apply le_trans (le_of_eq (by ring))
    (mul_le_mul_of_nonneg_right (le_abs_self _) oneHighNonneg)

theorem quotientDegreeFourPart_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments : Fin 4 → QuotientState parameters,
        rowsGradeNorm grade (quotientDegreeFourPart parameters arguments) ≤
          constant * oneHighArgumentSum grade arguments := by
  have orthNonneg : (0 : ℝ) ≤ 1 + orthogonalGradeConstant grade := by
    have orth := orthogonalGradeConstant_nonnegative grade
    linarith
  have quadFactorNonneg : (0 : ℝ) ≤ partialGradeConstant 3 +
      partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖ := by
    have p3 := partialGradeConstant_nonnegative 3
    have pg := partialGradeConstant_nonnegative (grade + 3)
    have tg := norm_nonneg tangentGeneratorMap
    linarith
  have quadNonneg : (0 : ℝ) ≤ (1 + orthogonalGradeConstant grade) *
      (productGradeConstant 2 grade * ‖determinantMultilinear‖) *
      (partialGradeConstant 3 + partialGradeConstant (grade + 3) +
        ‖tangentGeneratorMap‖) ^ 3 :=
    mul_nonneg (mul_nonneg orthNonneg (mul_nonneg (productGradeConstant_nonnegative _ _)
      (norm_nonneg _))) (pow_nonneg quadFactorNonneg 3)
  refine ⟨|(1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
      ‖determinantMultilinear‖) * (partialGradeConstant 3 +
        partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 3|, abs_nonneg _, ?_⟩
  intro arguments
  have oneHighNonneg := oneHighArgumentSum_nonneg grade arguments
  have valueForm : quotientDegreeFourPart parameters arguments =
      Pi.single 2 (stateScalar (arguments 0) • removeAngularCore parameters
        (actualMultilinearProduct parameters determinantMultilinear
          ![partialCore parameters 0 (stateField (arguments 1)),
            partialCore parameters 1 (stateField (arguments 2)),
            valueMapCore parameters tangentGeneratorMap (stateField (arguments 3))])) := rfl
  have quadLow : ∀ index, originalGradeNorm 3
      ((![partialCore parameters 0 (stateField (arguments 1)),
        partialCore parameters 1 (stateField (arguments 2)),
        valueMapCore parameters tangentGeneratorMap (stateField (arguments 3))]) index) ≤
      (partialGradeConstant 3 + partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) *
        stateNorm 4 ((fun position : Fin 3 => arguments position.succ) index) := by
    intro index
    fin_cases index
    · exact (factor_partial 0 (arguments 1) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg 4 _))
    · exact (factor_partial 1 (arguments 2) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg 4 _))
    · exact (factor_tangent (arguments 3) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          partialGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
  have quadHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![partialCore parameters 0 (stateField (arguments 1)),
        partialCore parameters 1 (stateField (arguments 2)),
        valueMapCore parameters tangentGeneratorMap (stateField (arguments 3))]) index) ≤
      (partialGradeConstant 3 + partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) *
        stateNorm (grade + 4) ((fun position : Fin 3 => arguments position.succ) index) := by
    intro index
    fin_cases index
    · exact (factor_partial 0 (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg _ _))
    · exact (factor_partial 1 (arguments 2) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          norm_nonneg tangentGeneratorMap]) (stateNorm_nonneg _ _))
    · exact (factor_tangent (arguments 3) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          partialGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg _ _))
  have quadInner := triple_post_argument_bound grade (1 + orthogonalGradeConstant grade)
    (fun field => removeAngularCore_bound field grade) orthNonneg determinantMultilinear
    ![partialCore parameters 0 (stateField (arguments 1)),
      partialCore parameters 1 (stateField (arguments 2)),
      valueMapCore parameters tangentGeneratorMap (stateField (arguments 3))]
    (fun position : Fin 3 => arguments position.succ) _ quadFactorNonneg quadLow quadHigh
  rw [valueForm, rowsGradeNorm_single, originalGradeNorm_smul]
  calc ‖stateScalar (arguments 0)‖ * originalGradeNorm grade
        (removeAngularCore parameters (actualMultilinearProduct parameters
          determinantMultilinear ![partialCore parameters 0 (stateField (arguments 1)),
            partialCore parameters 1 (stateField (arguments 2)),
            valueMapCore parameters tangentGeneratorMap (stateField (arguments 3))])) ≤
      ‖stateScalar (arguments 0)‖ * ((1 + orthogonalGradeConstant grade) *
        (productGradeConstant 2 grade * ‖determinantMultilinear‖) *
        (partialGradeConstant 3 + partialGradeConstant (grade + 3) +
          ‖tangentGeneratorMap‖) ^ 3 *
        oneHighArgumentSum grade (fun position : Fin 3 => arguments position.succ)) :=
        mul_le_mul_of_nonneg_left quadInner (norm_nonneg _)
    _ = (1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
        ‖determinantMultilinear‖) * (partialGradeConstant 3 +
          partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 3 *
        (‖stateScalar (arguments 0)‖ *
          oneHighArgumentSum grade (fun position : Fin 3 => arguments position.succ)) := by
        ring
    _ ≤ (1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
        ‖determinantMultilinear‖) * (partialGradeConstant 3 +
          partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 3 *
        oneHighArgumentSum grade arguments :=
        mul_le_mul_of_nonneg_left (scalar_wrap_argument_bound grade arguments) quadNonneg
    _ ≤ |(1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
        ‖determinantMultilinear‖) * (partialGradeConstant 3 +
          partialGradeConstant (grade + 3) + ‖tangentGeneratorMap‖) ^ 3| *
        oneHighArgumentSum grade arguments :=
        mul_le_mul_of_nonneg_right (le_abs_self _) oneHighNonneg

end Grad.NonlinearQuotientBounds
