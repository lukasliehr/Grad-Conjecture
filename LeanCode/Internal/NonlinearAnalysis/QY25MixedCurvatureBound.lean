import QY24InnerAllocationBounds

noncomputable section

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

theorem prod_directionNorm_le_inputOneHigh (high low : ℕ) (base : Input parameters) {order : ℕ}
    (directions : Fin order → Input parameters) :
    (∏ position, directionNorm low (directions position)) ≤ inputOneHigh high low base directions := by
  have productNonneg : 0 ≤ ∏ position, directionNorm low (directions position) :=
    Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _
  have baseNonneg := baseNorm_nonneg high base
  have first : (∏ position, directionNorm low (directions position)) ≤
      (1 + baseNorm high base) * ∏ position, directionNorm low (directions position) := by
    nlinarith
  exact first.trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => mul_nonneg (directionNorm_nonneg _ _)
      (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)))

/-- Curvature contributes only at orders zero and one. Its finite base
bound enters the constant, never the high state norm. -/
theorem referenceScalar_mixed_bound (high low order : ℕ) (curvatureBound : ℝ)
    (base : Input parameters) (directions : Fin order → Input parameters)
    (curvature : ‖base.2.1‖ ≤ curvatureBound) :
    ‖referenceScalar order base.2 (fun position => (directions position).2)‖ ≤
      (1 + |curvatureBound|) * inputOneHigh high low base directions := by
  rcases order with _ | _ | order
  · change ‖base.2.1‖ ≤ _
    simp only [inputOneHigh, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    nlinarith [baseNorm_nonneg high base, abs_nonneg curvatureBound, le_abs_self curvatureBound]
  · change ‖(directions 0).2.1‖ ≤ _
    have bracket : directionNorm high (directions 0) ≤ inputOneHigh high low base directions := by
      unfold inputOneHigh
      rw [Fin.sum_univ_one,
        (by decide : (Finset.univ.erase (0 : Fin 1)) = ∅), Finset.prod_empty, mul_one]
      exact le_add_of_nonneg_left
        (mul_nonneg (by linarith [baseNorm_nonneg high base])
          (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _))
    have curvatureDirection : ‖(directions 0).2.1‖ ≤ directionNorm high (directions 0) :=
      (norm_fst_le_jointNorm high (directions 0).2).trans
        (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    apply (curvatureDirection.trans bracket).trans
    have scale := mul_le_mul_of_nonneg_right
      (by linarith [abs_nonneg curvatureBound] : (1 : ℝ) ≤ 1 + |curvatureBound|)
      (inputOneHigh_nonneg high low base directions)
    simpa only [one_mul] using scale
  · change ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg (by positivity) (inputOneHigh_nonneg high low base directions)

end Grad.MixedQuotientComposition
