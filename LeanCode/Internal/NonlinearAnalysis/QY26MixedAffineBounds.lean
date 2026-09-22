import QY25MixedCurvatureBound

noncomputable section

set_option maxHeartbeats 300000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

def mixedTangentAffine : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → ACore parameters 3
  | 0, base, _ => chartTangentPart parameters base.2.2.1
  | 1, _, directions => chartTangentPart parameters (directions 0).2.2.1
  | _ + 2, _, _ => 0

def mixedFieldAffine : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → ACore parameters 3
  | 0, base, _ => base.2.2.2.1
  | 1, _, directions => (directions 0).2.2.2.1
  | _ + 2, _, _ => 0

def mixedPotentialAffine : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → ACore parameters 1
  | 0, base, _ => base.2.2.2.2
  | 1, _, directions => (directions 0).2.2.2.2
  | _ + 2, _, _ => 0

theorem directionNorm_le_inputOneHigh_one (high low : ℕ) (base : Input parameters)
    (directions : Fin 1 → Input parameters) :
    directionNorm high (directions 0) ≤ inputOneHigh high low base directions := by
  unfold inputOneHigh
  rw [Fin.sum_univ_one,
    (by decide : (Finset.univ.erase (0 : Fin 1)) = ∅), Finset.prod_empty, mul_one]
  exact le_add_of_nonneg_left
    (mul_nonneg (by linarith [baseNorm_nonneg high base])
      (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _))

theorem chartTangentPart_state_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ base : Input parameters,
      originalGradeNorm grade (chartTangentPart parameters base.2.2.1) ≤ constant * baseNorm grade base := by
  obtain ⟨constant, nonneg, bound⟩ := chartTangentPart_norm_le (parameters := parameters) grade
  have axis := axisConstant_pos.le
  refine ⟨constant * (Real.sqrt 2 ^ grade * axisConstant), by positivity, fun base => ?_⟩
  exact ((bound base.2.2.1).trans
    (mul_le_mul_of_nonneg_left (planarEnvelope_le_state grade base.2.2) nonneg)).trans_eq (by
      unfold baseNorm
      ring)

/-- The actual affine tangential term of the moving reference chart. -/
theorem mixedTangentAffine_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        originalGradeNorm grade (mixedTangentAffine order base directions) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := chartTangentPart_state_bound (parameters := parameters) grade
  refine ⟨constant, nonneg, ?_⟩
  rcases order with _ | _ | order
  · intro base directions
    change originalGradeNorm grade (chartTangentPart parameters base.2.2.1) ≤
      constant * inputOneHigh grade 4 base directions
    apply (bound base).trans
    apply mul_le_mul_of_nonneg_left _ nonneg
    simp only [inputOneHigh, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    linarith
  · intro base directions
    change originalGradeNorm grade (chartTangentPart parameters (directions 0).2.2.1) ≤
      constant * inputOneHigh grade 4 base directions
    apply (bound (directions 0)).trans
    apply mul_le_mul_of_nonneg_left _ nonneg
    exact (chartNorm_le_directionNorm grade (directions 0)).trans
      (directionNorm_le_inputOneHigh_one grade 4 base directions)
  · intro base directions
    change originalGradeNorm grade (0 : ACore parameters 3) ≤ _
    rw [originalGradeNorm_zero]
    exact mul_nonneg nonneg (inputOneHigh_nonneg _ _ _ _)

/-- The actual zero/one vector-field input tower used in the N18 product. -/
theorem mixedFieldAffine_bound (grade order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) :
    originalGradeNorm grade (mixedFieldAffine order base directions) ≤
      inputOneHigh grade 4 base directions := by
  rcases order with _ | _ | order
  · change originalGradeNorm grade base.2.2.2.1 ≤ _
    simp only [inputOneHigh, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    have field := field_le_chartStateNorm grade base.2.2
    change originalGradeNorm grade base.2.2.2.1 ≤ 1 + chartStateNorm grade base.2.2
    linarith
  · change originalGradeNorm grade (directions 0).2.2.2.1 ≤ _
    exact ((field_le_chartStateNorm grade (directions 0).2.2).trans
      (chartNorm_le_directionNorm grade (directions 0))).trans
      (directionNorm_le_inputOneHigh_one grade 4 base directions)
  · change originalGradeNorm grade (0 : ACore parameters 3) ≤ _
    rw [originalGradeNorm_zero]
    exact inputOneHigh_nonneg _ _ _ _

/-- The actual zero/one potential term of the moving reference chart. -/
theorem mixedPotentialAffine_bound (grade order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) :
    originalGradeNorm grade (mixedPotentialAffine order base directions) ≤
      inputOneHigh grade 4 base directions := by
  rcases order with _ | _ | order
  · change originalGradeNorm grade base.2.2.2.2 ≤ _
    simp only [inputOneHigh, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    have field := scalar_le_chartStateNorm grade base.2.2
    change originalGradeNorm grade base.2.2.2.2 ≤ 1 + chartStateNorm grade base.2.2
    linarith
  · change originalGradeNorm grade (directions 0).2.2.2.2 ≤ _
    exact ((scalar_le_chartStateNorm grade (directions 0).2.2).trans
      (chartNorm_le_directionNorm grade (directions 0))).trans
      (directionNorm_le_inputOneHigh_one grade 4 base directions)
  · change originalGradeNorm grade (0 : ACore parameters 1) ≤ _
    rw [originalGradeNorm_zero]
    exact inputOneHigh_nonneg _ _ _ _

end Grad.MixedQuotientComposition
