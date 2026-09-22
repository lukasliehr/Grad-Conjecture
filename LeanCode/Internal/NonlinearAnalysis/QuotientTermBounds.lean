import QuotientPolynomialDerivative

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

theorem originalGradeNorm_neg {dimension : ℕ} (grade : ℕ) (field : ACore parameters dimension) :
    originalGradeNorm grade (-field) = originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [map_neg, norm_neg]

/-- The one-high expression over the ordered derivative arguments. -/
def oneHighArgumentSum (grade : ℕ) {slots : ℕ}
    (arguments : Fin slots → QuotientState parameters) : ℝ :=
  ∑ slot, stateNorm (grade + 6) (arguments slot) *
    ∏ other ∈ Finset.univ.erase slot, stateNorm 4 (arguments other)

theorem oneHighArgumentSum_nonneg (grade : ℕ) {slots : ℕ}
    (arguments : Fin slots → QuotientState parameters) :
    0 ≤ oneHighArgumentSum grade arguments :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (stateNorm_nonneg _ _)
    (Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)))

theorem oneHighArgumentSum_single (grade : ℕ)
    (arguments : Fin 1 → QuotientState parameters) :
    oneHighArgumentSum grade arguments = stateNorm (grade + 6) (arguments 0) := by
  unfold oneHighArgumentSum
  rw [Fin.sum_univ_one]
  have empty : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro slot membership
    exact Finset.ne_of_mem_erase membership (Subsingleton.elim slot 0)
  rw [empty, Finset.prod_empty, mul_one]

/-- The full Q4 right-hand side over a base state and ordered directions. -/
def oneHighStateExpression (grade : ℕ) {order : ℕ} (base : QuotientState parameters)
    (directions : Fin order → QuotientState parameters) : ℝ :=
  (1 + stateNorm (grade + 6) base) * ∏ position, stateNorm 4 (directions position) +
    oneHighArgumentSum grade directions

theorem oneHighStateExpression_nonneg (grade : ℕ) {order : ℕ}
    (base : QuotientState parameters) (directions : Fin order → QuotientState parameters) :
    0 ≤ oneHighStateExpression grade base directions := by
  have baseNonneg := stateNorm_nonneg (grade + 6) base
  have productNonneg : (0 : ℝ) ≤ ∏ position, stateNorm 4 (directions position) :=
    Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)
  have sumNonneg := oneHighArgumentSum_nonneg grade directions
  unfold oneHighStateExpression
  nlinarith

/-- One uniform bound on the product one-high expression through per-slot
grade-shift factor bounds. -/
theorem oneHighExpression_le_argument {arity : ℕ} (grade : ℕ)
    (fields : Fin arity → ACore parameters 3)
    (arguments : Fin arity → QuotientState parameters) (factorConstant : ℝ)
    (nonnegative : 0 ≤ factorConstant)
    (lowBounds : ∀ index, originalGradeNorm 3 (fields index) ≤
      factorConstant * stateNorm 4 (arguments index))
    (highBounds : ∀ index, originalGradeNorm (grade + 3) (fields index) ≤
      factorConstant * stateNorm (grade + 4) (arguments index)) :
    oneHighExpression grade fields ≤
      factorConstant ^ arity * oneHighArgumentSum grade arguments := by
  rcases Nat.eq_zero_or_pos arity with zeroArity | positiveArity
  · subst zeroArity
    unfold oneHighExpression oneHighArgumentSum
    simp
  unfold oneHighExpression oneHighArgumentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  have highTerm : originalGradeNorm (grade + 3) (fields index) ≤
      factorConstant * stateNorm (grade + 6) (arguments index) :=
    (highBounds index).trans (mul_le_mul_of_nonneg_left
      (stateNorm_mono (by omega) (arguments index)) nonnegative)
  have productTerm : (∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other)) ≤
      factorConstant ^ (arity - 1) *
        ∏ other ∈ Finset.univ.erase index, stateNorm 4 (arguments other) := by
    have termwise : (∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other)) ≤
        ∏ other ∈ Finset.univ.erase index, factorConstant * stateNorm 4 (arguments other) :=
      Finset.prod_le_prod (fun other _ => originalGradeNorm_nonnegative _ _)
        (fun other _ => lowBounds other)
    apply termwise.trans_eq
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have powerSplit : factorConstant * factorConstant ^ (arity - 1) = factorConstant ^ arity := by
    rw [← pow_succ']
    congr 1
    omega
  have combined := mul_le_mul highTerm productTerm
    (Finset.prod_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _))
    (mul_nonneg nonnegative (stateNorm_nonneg _ _))
  apply combined.trans_eq
  calc (factorConstant * stateNorm (grade + 6) (arguments index)) *
        (factorConstant ^ (arity - 1) *
          ∏ other ∈ Finset.univ.erase index, stateNorm 4 (arguments other))
      = (factorConstant * factorConstant ^ (arity - 1)) *
        (stateNorm (grade + 6) (arguments index) *
          ∏ other ∈ Finset.univ.erase index, stateNorm 4 (arguments other)) := by ring
    _ = _ := by rw [powerSplit]

theorem factor_partialPlus (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (partialPlusCore parameters (stateField x)) ≤
      (2 * partialGradeConstant shift) * stateNorm (shift + 1) x :=
  (partialPlusCore_bound (stateField x) shift).trans
    (mul_le_mul_of_nonneg_left (originalGradeNorm_stateField_le (shift + 1) x)
      (mul_nonneg (by norm_num) (partialGradeConstant_nonnegative _)))

theorem factor_partialMinus (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (partialMinusCore parameters (stateField x)) ≤
      (2 * partialGradeConstant shift) * stateNorm (shift + 1) x :=
  (partialMinusCore_bound (stateField x) shift).trans
    (mul_le_mul_of_nonneg_left (originalGradeNorm_stateField_le (shift + 1) x)
      (mul_nonneg (by norm_num) (partialGradeConstant_nonnegative _)))

theorem factor_partial (direction : Fin 2) (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (partialCore parameters direction (stateField x)) ≤
      partialGradeConstant shift * stateNorm (shift + 1) x :=
  (partialCore_bound parameters direction (stateField x) shift).trans
    (mul_le_mul_of_nonneg_left (originalGradeNorm_stateField_le (shift + 1) x)
      (partialGradeConstant_nonnegative _))

theorem factor_rotation (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (rotationCore parameters (stateField x)) ≤
      vectorDerivativeGradeConstant shift * stateNorm (shift + 1) x :=
  (rotationCore_bound parameters (stateField x) shift).trans
    (mul_le_mul_of_nonneg_left (originalGradeNorm_stateField_le (shift + 1) x)
      (vectorDerivativeGradeConstant_nonnegative _))

theorem factor_timeDerivative (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (timeDerivativeCore parameters (stateField x)) ≤
      stateNorm (shift + 1) x :=
  (timeDerivativeCore_bound parameters shift (stateField x)).trans
    (originalGradeNorm_stateField_le (shift + 1) x)

theorem factor_tangent (x : QuotientState parameters) (shift : ℕ) :
    originalGradeNorm shift (valueMapCore parameters tangentGeneratorMap (stateField x)) ≤
      ‖tangentGeneratorMap‖ * stateNorm (shift + 1) x :=
  (valueMapCore_bound tangentGeneratorMap (stateField x) shift).trans
    ((mul_le_mul_of_nonneg_left (originalGradeNorm_stateField_le shift x)
      (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left
        ((stateNorm_mono (by omega) x)) (norm_nonneg _)))

/-- The pair-product terms of the polynomial through their factor bounds. -/
theorem pair_post_argument_bound {outputPost : ACore parameters 1 →ₗ[ℂ] ACore parameters 1}
    (grade : ℕ) (postConstant : ℝ)
    (postBound : ∀ field, originalGradeNorm grade (outputPost field) ≤
      postConstant * originalGradeNorm grade field)
    (postNonneg : 0 ≤ postConstant)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean 3) (ComplexEuclidean 1))
    (fields : Fin 2 → ACore parameters 3) (arguments : Fin 2 → QuotientState parameters)
    (factorConstant : ℝ) (factorNonneg : 0 ≤ factorConstant)
    (lowBounds : ∀ index, originalGradeNorm 3 (fields index) ≤
      factorConstant * stateNorm 4 (arguments index))
    (highBounds : ∀ index, originalGradeNorm (grade + 3) (fields index) ≤
      factorConstant * stateNorm (grade + 4) (arguments index)) :
    originalGradeNorm grade (outputPost (actualMultilinearProduct parameters multiplication fields)) ≤
      postConstant * (productGradeConstant 1 grade * ‖multiplication‖) * factorConstant ^ 2 *
        oneHighArgumentSum grade arguments := by
  apply (postBound _).trans
  have product := actualMultilinearProduct_bound parameters multiplication fields grade
  have oneHigh := oneHighExpression_le_argument grade fields arguments factorConstant
    factorNonneg lowBounds highBounds
  have productNonneg := mul_nonneg (productGradeConstant_nonnegative 1 grade) (norm_nonneg
    multiplication)
  calc postConstant * originalGradeNorm grade
        (actualMultilinearProduct parameters multiplication fields)
      ≤ postConstant * (productGradeConstant 1 grade * ‖multiplication‖ *
          oneHighExpression grade fields) :=
        mul_le_mul_of_nonneg_left product postNonneg
    _ ≤ postConstant * (productGradeConstant 1 grade * ‖multiplication‖ *
          (factorConstant ^ 2 * oneHighArgumentSum grade arguments)) := by
        apply mul_le_mul_of_nonneg_left _ postNonneg
        exact mul_le_mul_of_nonneg_left oneHigh productNonneg
    _ = postConstant * (productGradeConstant 1 grade * ‖multiplication‖) * factorConstant ^ 2 *
          oneHighArgumentSum grade arguments := by ring

/-- The triple-product terms of the polynomial through their factor bounds. -/
theorem triple_post_argument_bound {outputPost : ACore parameters 1 →ₗ[ℂ] ACore parameters 1}
    (grade : ℕ) (postConstant : ℝ)
    (postBound : ∀ field, originalGradeNorm grade (outputPost field) ≤
      postConstant * originalGradeNorm grade field)
    (postNonneg : 0 ≤ postConstant)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 3 => ComplexEuclidean 3) (ComplexEuclidean 1))
    (fields : Fin 3 → ACore parameters 3) (arguments : Fin 3 → QuotientState parameters)
    (factorConstant : ℝ) (factorNonneg : 0 ≤ factorConstant)
    (lowBounds : ∀ index, originalGradeNorm 3 (fields index) ≤
      factorConstant * stateNorm 4 (arguments index))
    (highBounds : ∀ index, originalGradeNorm (grade + 3) (fields index) ≤
      factorConstant * stateNorm (grade + 4) (arguments index)) :
    originalGradeNorm grade (outputPost (actualMultilinearProduct parameters multiplication fields)) ≤
      postConstant * (productGradeConstant 2 grade * ‖multiplication‖) * factorConstant ^ 3 *
        oneHighArgumentSum grade arguments := by
  apply (postBound _).trans
  have product := actualMultilinearProduct_bound parameters multiplication fields grade
  have oneHigh := oneHighExpression_le_argument grade fields arguments factorConstant
    factorNonneg lowBounds highBounds
  have productNonneg := mul_nonneg (productGradeConstant_nonnegative 2 grade) (norm_nonneg
    multiplication)
  calc postConstant * originalGradeNorm grade
        (actualMultilinearProduct parameters multiplication fields)
      ≤ postConstant * (productGradeConstant 2 grade * ‖multiplication‖ *
          oneHighExpression grade fields) :=
        mul_le_mul_of_nonneg_left product postNonneg
    _ ≤ postConstant * (productGradeConstant 2 grade * ‖multiplication‖ *
          (factorConstant ^ 3 * oneHighArgumentSum grade arguments)) := by
        apply mul_le_mul_of_nonneg_left _ postNonneg
        exact mul_le_mul_of_nonneg_left oneHigh productNonneg
    _ = postConstant * (productGradeConstant 2 grade * ‖multiplication‖) * factorConstant ^ 3 *
          oneHighArgumentSum grade arguments := by ring

theorem prod_erase_succ {count : ℕ} (values : Fin (count + 1) → ℝ) (position : Fin count) :
    (∏ slot ∈ Finset.univ.erase position.succ, values slot) =
      values 0 * ∏ slot ∈ Finset.univ.erase position, values slot.succ := by
  have decomposition : (Finset.univ.erase position.succ : Finset (Fin (count + 1))) =
      insert 0 ((Finset.univ.erase position).image Fin.succ) := by
    ext slot
    rw [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro paired
      rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨tail, ?_, rfl⟩
        rw [Finset.mem_erase]
        exact ⟨fun collide => paired.1 (by rw [collide]), Finset.mem_univ _⟩
    · intro membership
      rcases membership with rfl | ⟨tail, tailMembership, rfl⟩
      · exact ⟨(Fin.succ_ne_zero position).symm, Finset.mem_univ _⟩
      · rw [Finset.mem_erase] at tailMembership
        exact ⟨fun collide => tailMembership.1 (Fin.succ_injective _ collide),
          Finset.mem_univ _⟩
  rw [decomposition, Finset.prod_insert (by
      intro inside
      obtain ⟨tail, _, collapse⟩ := Finset.mem_image.mp inside
      exact Fin.succ_ne_zero tail collapse),
    Finset.prod_image (fun left _ right _ equal => Fin.succ_injective _ equal)]

/-- Lifting a one-high bound through the leading scalar slot. -/
theorem scalar_wrap_argument_bound {slots : ℕ} (grade : ℕ)
    (arguments : Fin (slots + 1) → QuotientState parameters) :
    ‖stateScalar (arguments 0)‖ *
        oneHighArgumentSum grade (fun position => arguments position.succ) ≤
      oneHighArgumentSum grade arguments := by
  have scalarLow := norm_stateScalar_le 4 (arguments 0)
  unfold oneHighArgumentSum
  rw [Finset.mul_sum]
  have termwise : ∀ position : Fin slots,
      ‖stateScalar (arguments 0)‖ * (stateNorm (grade + 6) (arguments position.succ) *
        ∏ other ∈ Finset.univ.erase position, stateNorm 4 (arguments other.succ)) ≤
      stateNorm (grade + 6) (arguments position.succ) *
        ∏ other ∈ Finset.univ.erase position.succ, stateNorm 4 (arguments other) := by
    intro position
    rw [prod_erase_succ (fun slot => stateNorm 4 (arguments slot)) position]
    have scalarStep : ‖stateScalar (arguments 0)‖ *
        (stateNorm (grade + 6) (arguments position.succ) *
          ∏ other ∈ Finset.univ.erase position, stateNorm 4 (arguments other.succ)) ≤
        stateNorm 4 (arguments 0) * (stateNorm (grade + 6) (arguments position.succ) *
          ∏ other ∈ Finset.univ.erase position, stateNorm 4 (arguments other.succ)) :=
      mul_le_mul_of_nonneg_right scalarLow (mul_nonneg (stateNorm_nonneg _ _)
        (Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)))
    apply scalarStep.trans_eq
    ring
  apply (Finset.sum_le_sum (fun position _ => termwise position)).trans
  rw [Fin.sum_univ_succ (f := fun slot => stateNorm (grade + 6) (arguments slot) *
    ∏ other ∈ Finset.univ.erase slot, stateNorm 4 (arguments other))]
  have headNonneg : 0 ≤ stateNorm (grade + 6) (arguments 0) *
      ∏ other ∈ Finset.univ.erase (0 : Fin (slots + 1)), stateNorm 4 (arguments other) :=
    mul_nonneg (stateNorm_nonneg _ _)
      (Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _))
  linarith

end Grad.NonlinearQuotientBounds
