import QY23TransferCoreBounds

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-- A single high root block times all complementary low seed directions
is bounded by the original full one-high expression. -/
theorem inputOneHigh_fiber_mul_compl_le (high low : ℕ) (base : Input parameters)
    {order slots : ℕ} (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → Input parameters) :
    inputOneHigh high low base (fiberTuple assignment slot directions) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm low (directions position)) ≤
      inputOneHigh high low base directions := by
  unfold inputOneHigh fiberTuple
  rw [prod_fiber_eq assignment slot (fun position => directionNorm low (directions position)),
    sum_fiber_oneHigh_eq assignment slot (fun position => directionNorm high (directions position))
      (fun position => directionNorm low (directions position)),
    add_mul, mul_assoc, prod_fiber_mul_prod_compl, Finset.sum_mul]
  apply add_le_add le_rfl
  calc
    _ = ∑ position ∈ assignmentFiber assignment slot,
        directionNorm high (directions position) *
          ∏ other ∈ Finset.univ.erase position, directionNorm low (directions other) := by
      apply Finset.sum_congr rfl
      intro position member
      rw [mul_assoc, prod_erase_fiber_mul_prod_compl assignment slot _ position member]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => mul_nonneg (directionNorm_nonneg _ _)
        (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _))

theorem mixedRootDerivative_uniform_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ count, count ≤ order →
      ∀ (base : Input parameters) (directions : Fin count → Input parameters),
        ChartAxisCondition base.2.2 →
        coefficientEnvelope grade
          (rootDerivativeFamily count base.2.2.1 (fun position => (directions position).2.2.1)) ≤
          constant * inputOneHigh grade 4 base directions := by
  choose constants nonneg bounds using mixedRootDerivative_bound (parameters := parameters) grade
  refine ⟨∑ count ∈ Finset.range (order + 1), constants count,
    Finset.sum_nonneg fun count _ => nonneg count, ?_⟩
  intro count countLe base directions axis
  apply (bounds count base directions axis).trans
  apply mul_le_mul_of_nonneg_right _ (inputOneHigh_nonneg _ _ _ _)
  exact Finset.single_le_sum (fun c _ => nonneg c) (Finset.mem_range.mpr (by omega))

/-- The actual root derivative in any assignment fiber, including the
empty fiber, with the complementary seed factors attached. -/
theorem mixedRootDerivative_fiber_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        ChartAxisCondition base.2.2 →
        ∀ {slots : ℕ} (assignment : Fin order → Fin slots) (slot : Fin slots),
        coefficientEnvelope grade
          (rootDerivativeFamily (assignmentFiber assignment slot).card base.2.2.1
            (fun position => (fiberTuple assignment slot directions position).2.2.1)) *
          (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := mixedRootDerivative_uniform_bound (parameters := parameters) grade order
  refine ⟨constant, nonneg, fun base directions axis slots assignment slot => ?_⟩
  have cardLe : (assignmentFiber assignment slot).card ≤ order :=
    (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
  calc
    _ ≤ (constant * inputOneHigh grade 4 base (fiberTuple assignment slot directions)) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)) :=
      mul_le_mul_of_nonneg_right
        (bound _ cardLe base (fiberTuple assignment slot directions) axis)
        (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
    _ ≤ constant * inputOneHigh grade 4 base directions := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (inputOneHigh_fiber_mul_compl_le grade 4 base assignment slot directions) nonneg

end Grad.MixedQuotientComposition
