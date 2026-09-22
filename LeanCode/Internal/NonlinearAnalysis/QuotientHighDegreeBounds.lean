import QuotientLowDegreeBounds

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

theorem rowsGradeNorm_four_singles (grade : ℕ) (rowA rowB rowC rowD : Fin 4)
    (first second third fourth : ACore parameters 1) :
    rowsGradeNorm grade (Pi.single rowA first + Pi.single rowB second +
        Pi.single rowC third + Pi.single rowD fourth) ≤
      originalGradeNorm grade first + originalGradeNorm grade second +
        originalGradeNorm grade third + originalGradeNorm grade fourth := by
  apply (rowsGradeNorm_add_le grade _ _).trans
  apply (add_le_add ((rowsGradeNorm_add_le grade _ _).trans (add_le_add
    ((rowsGradeNorm_add_le grade _ _).trans (add_le_add
      (le_of_eq (rowsGradeNorm_single grade rowA first))
      (le_of_eq (rowsGradeNorm_single grade rowB second))))
    (le_of_eq (rowsGradeNorm_single grade rowC third))))
    (le_of_eq (rowsGradeNorm_single grade rowD fourth))).trans
  exact le_rfl

theorem rowsGradeNorm_two_singles (grade : ℕ) (rowA rowB : Fin 4)
    (first second : ACore parameters 1) :
    rowsGradeNorm grade (Pi.single rowA first + Pi.single rowB second) ≤
      originalGradeNorm grade first + originalGradeNorm grade second := by
  apply (rowsGradeNorm_add_le grade _ _).trans
  exact add_le_add (le_of_eq (rowsGradeNorm_single grade rowA first))
    (le_of_eq (rowsGradeNorm_single grade rowB second))

theorem oneHighExpression_triple (first second third : ACore parameters 3) (grade : ℕ) :
    oneHighExpression grade ![first, second, third] =
      originalGradeNorm (grade + 3) first *
          (originalGradeNorm 3 second * originalGradeNorm 3 third) +
        originalGradeNorm (grade + 3) second *
          (originalGradeNorm 3 first * originalGradeNorm 3 third) +
          originalGradeNorm (grade + 3) third *
            (originalGradeNorm 3 first * originalGradeNorm 3 second) := by
  have eraseZero : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by
    ext slot
    fin_cases slot <;> simp [Fin.ext_iff]
  have eraseOne : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by
    ext slot
    fin_cases slot <;> simp [Fin.ext_iff]
  have eraseTwo : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by
    ext slot
    fin_cases slot <;> simp [Fin.ext_iff]
  have insertOneTwo : ∀ values : Fin 3 → ℝ,
      (∏ slot ∈ ({1, 2} : Finset (Fin 3)), values slot) = values 1 * values 2 := by
    intro values
    rw [show ({1, 2} : Finset (Fin 3)) = insert 1 {2} from rfl,
      Finset.prod_insert (by simp [Fin.ext_iff]), Finset.prod_singleton]
  have insertZeroTwo : ∀ values : Fin 3 → ℝ,
      (∏ slot ∈ ({0, 2} : Finset (Fin 3)), values slot) = values 0 * values 2 := by
    intro values
    rw [show ({0, 2} : Finset (Fin 3)) = insert 0 {2} from rfl,
      Finset.prod_insert (by simp [Fin.ext_iff]), Finset.prod_singleton]
  have insertZeroOne : ∀ values : Fin 3 → ℝ,
      (∏ slot ∈ ({0, 1} : Finset (Fin 3)), values slot) = values 0 * values 1 := by
    intro values
    rw [show ({0, 1} : Finset (Fin 3)) = insert 0 {1} from rfl,
      Finset.prod_insert (by simp), Finset.prod_singleton]
  unfold oneHighExpression
  rw [Fin.sum_univ_three, eraseZero, eraseOne, eraseTwo, insertOneTwo, insertZeroTwo,
    insertZeroOne]
  simp

theorem quotientDegreeTwoPart_bound (cellLength : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments : Fin 2 → QuotientState parameters,
        rowsGradeNorm grade (quotientDegreeTwoPart parameters cellLength arguments) ≤
          constant * oneHighArgumentSum grade arguments := by
  have pairFactorNonneg : (0 : ℝ) ≤ 2 * partialGradeConstant 3 +
      2 * partialGradeConstant (grade + 3) + vectorDerivativeGradeConstant 3 +
      vectorDerivativeGradeConstant (grade + 3) + 1 := by
    have p3 := partialGradeConstant_nonnegative 3
    have pg := partialGradeConstant_nonnegative (grade + 3)
    have v3 := vectorDerivativeGradeConstant_nonnegative 3
    have vg := vectorDerivativeGradeConstant_nonnegative (grade + 3)
    linarith
  have orthNonneg : (0 : ℝ) ≤ 1 + orthogonalGradeConstant grade := by
    have orth := orthogonalGradeConstant_nonnegative grade
    linarith
  have identityBound : ∀ field : ACore parameters 1,
      originalGradeNorm grade ((LinearMap.id : ACore parameters 1 →ₗ[ℂ] ACore parameters 1)
        field) ≤ 1 * originalGradeNorm grade field := by
    intro field
    rw [LinearMap.id_apply, one_mul]
  refine ⟨|1 * (productGradeConstant 1 grade * ‖physicalDotProduct‖) *
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) ^ 2 +
    2 * coordinateGradeConstant grade * (radialQuotientConstant grade * ‖physicalDotProduct‖) +
    (1 * (productGradeConstant 1 grade * ‖physicalDotProduct‖) *
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) ^ 2 +
    2 * coordinateGradeConstant grade * (radialQuotientConstant grade * ‖physicalDotProduct‖)) +
    (1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
      ‖determinantMultilinear‖) * (partialGradeConstant (grade + 3) *
        (partialGradeConstant 3 * (|cellLength| *
          originalGradeNorm 3 (eTConstantCore parameters))) +
      partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
        (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) +
      |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
        (partialGradeConstant 3 * partialGradeConstant 3)) +
    (1 + orthogonalGradeConstant grade) * (productGradeConstant 1 grade *
      ‖physicalDotProduct‖) * (2 * partialGradeConstant 3 +
        2 * partialGradeConstant (grade + 3) + vectorDerivativeGradeConstant 3 +
        vectorDerivativeGradeConstant (grade + 3) + 1) ^ 2|, abs_nonneg _, ?_⟩
  intro arguments
  have oneHighNonneg := oneHighArgumentSum_nonneg grade arguments
  have valueForm : quotientDegreeTwoPart parameters cellLength arguments =
      Pi.single 0 (-(actualMultilinearProduct parameters physicalDotProduct
          ![partialPlusCore parameters (stateField (arguments 0)),
            rotationCore parameters (stateField (arguments 1))]) +
        zMulCore parameters (bilinearRadialCore parameters physicalDotProduct
          (stateField (arguments 0)) (stateField (arguments 1)))) +
      Pi.single 1 (-(actualMultilinearProduct parameters physicalDotProduct
          ![partialMinusCore parameters (stateField (arguments 0)),
            rotationCore parameters (stateField (arguments 1))]) +
        starZMulCore parameters (bilinearRadialCore parameters physicalDotProduct
          (stateField (arguments 0)) (stateField (arguments 1)))) +
      Pi.single 2 (removeAngularCore parameters (actualMultilinearProduct parameters
          determinantMultilinear ![partialCore parameters 0 (stateField (arguments 0)),
            partialCore parameters 1 (stateField (arguments 1)),
            (cellLength : ℂ) • eTConstantCore parameters])) +
      Pi.single 3 (removeAngularCore parameters (actualMultilinearProduct parameters
          physicalDotProduct ![rotationCore parameters (stateField (arguments 0)),
            timeDerivativeCore parameters (stateField (arguments 1))])) := rfl
  have plusLow : ∀ index, originalGradeNorm 3
      ((![partialPlusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm 4 (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partialPlus (arguments 0) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
    · exact (factor_rotation (arguments 1) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
  have plusHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![partialPlusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm (grade + 4) (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partialPlus (arguments 0) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg _ _))
    · exact (factor_rotation (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          partialGradeConstant_nonnegative (grade + 3),
          vectorDerivativeGradeConstant_nonnegative 3]) (stateNorm_nonneg _ _))
  have minusLow : ∀ index, originalGradeNorm 3
      ((![partialMinusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm 4 (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partialMinus (arguments 0) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
    · exact (factor_rotation (arguments 1) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
  have minusHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![partialMinusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm (grade + 4) (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_partialMinus (arguments 0) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg _ _))
    · exact (factor_rotation (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative 3,
          partialGradeConstant_nonnegative (grade + 3),
          vectorDerivativeGradeConstant_nonnegative 3]) (stateNorm_nonneg _ _))
  have timeLow : ∀ index, originalGradeNorm 3
      ((![rotationCore parameters (stateField (arguments 0)),
        timeDerivativeCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm 4 (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_rotation (arguments 0) 3).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative (grade + 3)]) (stateNorm_nonneg 4 _))
    · apply (factor_timeDerivative (arguments 1) 3).trans
      apply le_mul_of_one_le_left (stateNorm_nonneg 4 _)
      linarith [partialGradeConstant_nonnegative (grade + 3),
        partialGradeConstant_nonnegative 3,
        vectorDerivativeGradeConstant_nonnegative (grade + 3),
        vectorDerivativeGradeConstant_nonnegative 3]
  have timeHigh : ∀ index, originalGradeNorm (grade + 3)
      ((![rotationCore parameters (stateField (arguments 0)),
        timeDerivativeCore parameters (stateField (arguments 1))]) index) ≤
      (2 * partialGradeConstant 3 + 2 * partialGradeConstant (grade + 3) +
        vectorDerivativeGradeConstant 3 + vectorDerivativeGradeConstant (grade + 3) + 1) *
        stateNorm (grade + 4) (arguments index) := by
    intro index
    fin_cases index
    · exact (factor_rotation (arguments 0) (grade + 3)).trans (mul_le_mul_of_nonneg_right
        (by linarith [partialGradeConstant_nonnegative (grade + 3),
          partialGradeConstant_nonnegative 3,
          vectorDerivativeGradeConstant_nonnegative 3]) (stateNorm_nonneg _ _))
    · apply (factor_timeDerivative (arguments 1) (grade + 3)).trans
      apply le_mul_of_one_le_left (stateNorm_nonneg _ _)
      linarith [partialGradeConstant_nonnegative (grade + 3),
        partialGradeConstant_nonnegative 3,
        vectorDerivativeGradeConstant_nonnegative (grade + 3),
        vectorDerivativeGradeConstant_nonnegative 3]
  have radialInner : originalGradeNorm grade (bilinearRadialCore parameters physicalDotProduct
      (stateField (arguments 0)) (stateField (arguments 1))) ≤
      radialQuotientConstant grade * ‖physicalDotProduct‖ *
        oneHighArgumentSum grade arguments := by
    apply (bilinearRadialCore_bound parameters physicalDotProduct _ _ grade).trans
    rw [oneHighArgumentSum_pair]
    have firstPair : originalGradeNorm (grade + 6) (stateField (arguments 0)) *
        originalGradeNorm 4 (stateField (arguments 1)) ≤
        stateNorm (grade + 6) (arguments 0) * stateNorm 4 (arguments 1) :=
      mul_le_mul (originalGradeNorm_stateField_le _ _) (originalGradeNorm_stateField_le _ _)
        (originalGradeNorm_nonnegative _ _) (stateNorm_nonneg _ _)
    have secondPair : originalGradeNorm 4 (stateField (arguments 0)) *
        originalGradeNorm (grade + 6) (stateField (arguments 1)) ≤
        stateNorm (grade + 6) (arguments 1) * stateNorm 4 (arguments 0) := by
      have raw : originalGradeNorm 4 (stateField (arguments 0)) *
          originalGradeNorm (grade + 6) (stateField (arguments 1)) ≤
          stateNorm 4 (arguments 0) * stateNorm (grade + 6) (arguments 1) :=
        mul_le_mul (originalGradeNorm_stateField_le _ _) (originalGradeNorm_stateField_le _ _)
          (originalGradeNorm_nonnegative _ _) (stateNorm_nonneg _ _)
      exact raw.trans_eq (mul_comm _ _)
    exact mul_le_mul_of_nonneg_left (add_le_add firstPair secondPair)
      (mul_nonneg (radialQuotientConstant_nonnegative _) (norm_nonneg _))
  have zRowBound : originalGradeNorm grade (zMulCore parameters
      (bilinearRadialCore parameters physicalDotProduct (stateField (arguments 0))
        (stateField (arguments 1)))) ≤
      2 * coordinateGradeConstant grade *
        (radialQuotientConstant grade * ‖physicalDotProduct‖) *
          oneHighArgumentSum grade arguments := by
    apply (zMulCore_bound _ grade).trans
    have coefNonneg : (0 : ℝ) ≤ 2 * coordinateGradeConstant grade :=
      mul_nonneg (by norm_num) (coordinateGradeConstant_nonnegative _)
    exact (mul_le_mul_of_nonneg_left radialInner coefNonneg).trans_eq (by ring)
  have starRowBound : originalGradeNorm grade (starZMulCore parameters
      (bilinearRadialCore parameters physicalDotProduct (stateField (arguments 0))
        (stateField (arguments 1)))) ≤
      2 * coordinateGradeConstant grade *
        (radialQuotientConstant grade * ‖physicalDotProduct‖) *
          oneHighArgumentSum grade arguments := by
    apply (starZMulCore_bound _ grade).trans
    have coefNonneg : (0 : ℝ) ≤ 2 * coordinateGradeConstant grade :=
      mul_nonneg (by norm_num) (coordinateGradeConstant_nonnegative _)
    exact (mul_le_mul_of_nonneg_left radialInner coefNonneg).trans_eq (by ring)
  have plusProduct := pair_post_argument_bound grade 1 identityBound zero_le_one
    physicalDotProduct ![partialPlusCore parameters (stateField (arguments 0)),
      rotationCore parameters (stateField (arguments 1))] arguments _
    pairFactorNonneg plusLow plusHigh
  have minusProduct := pair_post_argument_bound grade 1 identityBound zero_le_one
    physicalDotProduct ![partialMinusCore parameters (stateField (arguments 0)),
      rotationCore parameters (stateField (arguments 1))] arguments _
    pairFactorNonneg minusLow minusHigh
  have timeProduct := pair_post_argument_bound grade (1 + orthogonalGradeConstant grade)
    (fun field => removeAngularCore_bound field grade) orthNonneg
    physicalDotProduct ![rotationCore parameters (stateField (arguments 0)),
      timeDerivativeCore parameters (stateField (arguments 1))] arguments _
    pairFactorNonneg timeLow timeHigh
  have scaledLow : originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters) =
      |cellLength| * originalGradeNorm 3 (eTConstantCore parameters) := by
    rw [originalGradeNorm_smul, Complex.norm_real, Real.norm_eq_abs]
  have scaledHigh : originalGradeNorm (grade + 3)
      ((cellLength : ℂ) • eTConstantCore parameters) =
      |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) := by
    rw [originalGradeNorm_smul, Complex.norm_real, Real.norm_eq_abs]
  have pairInSum : stateNorm (grade + 6) (arguments 0) * stateNorm 4 (arguments 1) ≤
      oneHighArgumentSum grade arguments := by
    rw [oneHighArgumentSum_pair]
    have tail : (0 : ℝ) ≤ stateNorm (grade + 6) (arguments 1) * stateNorm 4 (arguments 0) :=
      mul_nonneg (stateNorm_nonneg _ _) (stateNorm_nonneg _ _)
    linarith
  have pairInSum' : stateNorm (grade + 6) (arguments 1) * stateNorm 4 (arguments 0) ≤
      oneHighArgumentSum grade arguments := by
    rw [oneHighArgumentSum_pair]
    have head : (0 : ℝ) ≤ stateNorm (grade + 6) (arguments 0) * stateNorm 4 (arguments 1) :=
      mul_nonneg (stateNorm_nonneg _ _) (stateNorm_nonneg _ _)
    linarith
  have eTNormNonneg3 := originalGradeNorm_nonnegative 3 (eTConstantCore parameters)
  have eTNormNonnegHigh := originalGradeNorm_nonnegative (grade + 3) (eTConstantCore parameters)
  have detRowBound : originalGradeNorm grade (removeAngularCore parameters
      (actualMultilinearProduct parameters determinantMultilinear
        ![partialCore parameters 0 (stateField (arguments 0)),
          partialCore parameters 1 (stateField (arguments 1)),
          (cellLength : ℂ) • eTConstantCore parameters])) ≤
      (1 + orthogonalGradeConstant grade) * (productGradeConstant 2 grade *
        ‖determinantMultilinear‖) * (partialGradeConstant (grade + 3) *
          (partialGradeConstant 3 * (|cellLength| *
            originalGradeNorm 3 (eTConstantCore parameters))) +
        partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) +
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
          (partialGradeConstant 3 * partialGradeConstant 3)) *
        oneHighArgumentSum grade arguments := by
    have firstHigh : originalGradeNorm (grade + 3)
        (partialCore parameters 0 (stateField (arguments 0))) ≤
        partialGradeConstant (grade + 3) * stateNorm (grade + 6) (arguments 0) :=
      (factor_partial 0 (arguments 0) (grade + 3)).trans (mul_le_mul_of_nonneg_left
        (stateNorm_mono (by omega) _) (partialGradeConstant_nonnegative _))
    have firstLow : originalGradeNorm 3
        (partialCore parameters 0 (stateField (arguments 0))) ≤
        partialGradeConstant 3 * stateNorm 4 (arguments 0) :=
      factor_partial 0 (arguments 0) 3
    have secondHigh : originalGradeNorm (grade + 3)
        (partialCore parameters 1 (stateField (arguments 1))) ≤
        partialGradeConstant (grade + 3) * stateNorm (grade + 6) (arguments 1) :=
      (factor_partial 1 (arguments 1) (grade + 3)).trans (mul_le_mul_of_nonneg_left
        (stateNorm_mono (by omega) _) (partialGradeConstant_nonnegative _))
    have secondLow : originalGradeNorm 3
        (partialCore parameters 1 (stateField (arguments 1))) ≤
        partialGradeConstant 3 * stateNorm 4 (arguments 1) :=
      factor_partial 1 (arguments 1) 3
    have pieceA : originalGradeNorm (grade + 3)
        (partialCore parameters 0 (stateField (arguments 0))) *
        (originalGradeNorm 3 (partialCore parameters 1 (stateField (arguments 1))) *
          originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters)) ≤
        partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) *
          oneHighArgumentSum grade arguments := by
      rw [scaledLow]
      have raw := mul_le_mul firstHigh (mul_le_mul_of_nonneg_right secondLow
          (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))
        (mul_nonneg (originalGradeNorm_nonnegative _ _)
          (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))
        (mul_nonneg (partialGradeConstant_nonnegative _) (stateNorm_nonneg _ _))
      apply raw.trans
      apply le_trans (le_of_eq (by ring))
        (mul_le_mul_of_nonneg_left pairInSum
          (mul_nonneg (partialGradeConstant_nonnegative _)
            (mul_nonneg (partialGradeConstant_nonnegative _)
              (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))))
    have pieceB : originalGradeNorm (grade + 3)
        (partialCore parameters 1 (stateField (arguments 1))) *
        (originalGradeNorm 3 (partialCore parameters 0 (stateField (arguments 0))) *
          originalGradeNorm 3 ((cellLength : ℂ) • eTConstantCore parameters)) ≤
        partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
          (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) *
          oneHighArgumentSum grade arguments := by
      rw [scaledLow]
      have raw := mul_le_mul secondHigh (mul_le_mul_of_nonneg_right firstLow
          (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))
        (mul_nonneg (originalGradeNorm_nonnegative _ _)
          (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))
        (mul_nonneg (partialGradeConstant_nonnegative _) (stateNorm_nonneg _ _))
      apply raw.trans
      apply le_trans (le_of_eq (by ring))
        (mul_le_mul_of_nonneg_left pairInSum'
          (mul_nonneg (partialGradeConstant_nonnegative _)
            (mul_nonneg (partialGradeConstant_nonnegative _)
              (mul_nonneg (abs_nonneg cellLength) eTNormNonneg3))))
    have pieceC : originalGradeNorm (grade + 3)
        ((cellLength : ℂ) • eTConstantCore parameters) *
        (originalGradeNorm 3 (partialCore parameters 0 (stateField (arguments 0))) *
          originalGradeNorm 3 (partialCore parameters 1 (stateField (arguments 1)))) ≤
        |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
          (partialGradeConstant 3 * partialGradeConstant 3) *
          oneHighArgumentSum grade arguments := by
      rw [scaledHigh]
      have lowRelaxed : originalGradeNorm 3
          (partialCore parameters 0 (stateField (arguments 0))) ≤
          partialGradeConstant 3 * stateNorm (grade + 6) (arguments 0) :=
        firstLow.trans (mul_le_mul_of_nonneg_left (stateNorm_mono (by omega) _)
          (partialGradeConstant_nonnegative _))
      have raw := mul_le_mul_of_nonneg_left (mul_le_mul lowRelaxed secondLow
          (originalGradeNorm_nonnegative _ _)
          (mul_nonneg (partialGradeConstant_nonnegative _) (stateNorm_nonneg _ _)))
        (mul_nonneg (abs_nonneg cellLength) eTNormNonnegHigh)
      apply raw.trans
      apply le_trans (le_of_eq (by ring))
        (mul_le_mul_of_nonneg_left pairInSum
          (mul_nonneg (mul_nonneg (abs_nonneg cellLength) eTNormNonnegHigh)
            (mul_nonneg (partialGradeConstant_nonnegative _)
              (partialGradeConstant_nonnegative _))))
    apply (removeAngularCore_bound _ grade).trans
    have inner : originalGradeNorm grade (actualMultilinearProduct parameters
        determinantMultilinear ![partialCore parameters 0 (stateField (arguments 0)),
          partialCore parameters 1 (stateField (arguments 1)),
          (cellLength : ℂ) • eTConstantCore parameters]) ≤
        productGradeConstant 2 grade * ‖determinantMultilinear‖ *
          ((partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
            (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) +
          partialGradeConstant (grade + 3) * (partialGradeConstant 3 *
            (|cellLength| * originalGradeNorm 3 (eTConstantCore parameters))) +
          |cellLength| * originalGradeNorm (grade + 3) (eTConstantCore parameters) *
            (partialGradeConstant 3 * partialGradeConstant 3)) *
          oneHighArgumentSum grade arguments) := by
      apply (actualMultilinearProduct_bound parameters determinantMultilinear _ grade).trans
      rw [oneHighExpression_triple]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (productGradeConstant_nonnegative _ _) (norm_nonneg _))
      exact (add_le_add (add_le_add pieceA pieceB) pieceC).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left inner orthNonneg).trans_eq (by ring)
  rw [valueForm]
  have negOne : originalGradeNorm grade (-(actualMultilinearProduct parameters
      physicalDotProduct ![partialPlusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) +
      zMulCore parameters (bilinearRadialCore parameters physicalDotProduct
        (stateField (arguments 0)) (stateField (arguments 1)))) ≤
      originalGradeNorm grade (actualMultilinearProduct parameters physicalDotProduct
        ![partialPlusCore parameters (stateField (arguments 0)),
          rotationCore parameters (stateField (arguments 1))]) +
      originalGradeNorm grade (zMulCore parameters (bilinearRadialCore parameters
        physicalDotProduct (stateField (arguments 0)) (stateField (arguments 1)))) := by
    have split := originalGradeNorm_add_le grade
      (-(actualMultilinearProduct parameters physicalDotProduct
        ![partialPlusCore parameters (stateField (arguments 0)),
          rotationCore parameters (stateField (arguments 1))]))
      (zMulCore parameters (bilinearRadialCore parameters physicalDotProduct
        (stateField (arguments 0)) (stateField (arguments 1))))
    rwa [originalGradeNorm_neg] at split
  have negTwo : originalGradeNorm grade (-(actualMultilinearProduct parameters
      physicalDotProduct ![partialMinusCore parameters (stateField (arguments 0)),
        rotationCore parameters (stateField (arguments 1))]) +
      starZMulCore parameters (bilinearRadialCore parameters physicalDotProduct
        (stateField (arguments 0)) (stateField (arguments 1)))) ≤
      originalGradeNorm grade (actualMultilinearProduct parameters physicalDotProduct
        ![partialMinusCore parameters (stateField (arguments 0)),
          rotationCore parameters (stateField (arguments 1))]) +
      originalGradeNorm grade (starZMulCore parameters (bilinearRadialCore parameters
        physicalDotProduct (stateField (arguments 0)) (stateField (arguments 1)))) := by
    have split := originalGradeNorm_add_le grade
      (-(actualMultilinearProduct parameters physicalDotProduct
        ![partialMinusCore parameters (stateField (arguments 0)),
          rotationCore parameters (stateField (arguments 1))]))
      (starZMulCore parameters (bilinearRadialCore parameters physicalDotProduct
        (stateField (arguments 0)) (stateField (arguments 1))))
    rwa [originalGradeNorm_neg] at split
  apply (rowsGradeNorm_four_singles grade 0 1 2 3 _ _ _ _).trans
  apply (add_le_add (add_le_add (add_le_add negOne negTwo) le_rfl) le_rfl).trans
  have summed := add_le_add (add_le_add (add_le_add
    (add_le_add plusProduct zRowBound) (add_le_add minusProduct starRowBound))
    detRowBound) timeProduct
  apply summed.trans
  apply le_trans (le_of_eq (by ring))
    (mul_le_mul_of_nonneg_right (le_abs_self _) oneHighNonneg)

end Grad.NonlinearQuotientBounds
