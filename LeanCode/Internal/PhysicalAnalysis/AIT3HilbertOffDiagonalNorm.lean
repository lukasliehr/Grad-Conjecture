import AIT2ActualLowOffDiagonalResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse

section HilbertProduct
variable {H L : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup L] [NormedSpace ℂ L]

/-- Internal product algebra; the final consumer supplies the actual two
physical solution maps. -/
def hilbertOffDiagonal (upper : L →L[ℂ] H) (lower : H →L[ℂ] L) :
    WithLp 2 (H × L) →L[ℂ] WithLp 2 (H × L) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H L).symm.toContinuousLinearMap.comp
    ((upper.comp ((ContinuousLinearMap.snd ℂ H L).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H L).toContinuousLinearMap)).prod
     (lower.comp ((ContinuousLinearMap.fst ℂ H L).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H L).toContinuousLinearMap)))

theorem hilbertOffDiagonal_high (upper : L →L[ℂ] H) (lower : H →L[ℂ] L)
    (field : WithLp 2 (H × L)) :
    (hilbertOffDiagonal upper lower field).ofLp.1 = upper field.ofLp.2 := rfl

theorem hilbertOffDiagonal_low (upper : L →L[ℂ] H) (lower : H →L[ℂ] L)
    (field : WithLp 2 (H × L)) :
    (hilbertOffDiagonal upper lower field).ofLp.2 = lower field.ofLp.1 := rfl

theorem hilbertOffDiagonal_norm (upper : L →L[ℂ] H) (lower : H →L[ℂ] L)
    (upperConstant lowerConstant budget : ℝ)
    (upperNonnegative : 0 ≤ upperConstant)
    (budgetNonnegative : 0 ≤ budget)
    (upperBound : ∀ field, ‖upper field‖ ≤ upperConstant * budget * ‖field‖)
    (lowerBound : ∀ field, ‖lower field‖ ≤ lowerConstant * budget * ‖field‖) :
    ‖hilbertOffDiagonal upper lower‖ ≤ max upperConstant lowerConstant * budget := by
  let coefficient := max upperConstant lowerConstant * budget
  have coefficientNonnegative : 0 ≤ coefficient :=
    mul_nonneg (le_trans upperNonnegative (le_max_left _ _)) budgetNonnegative
  apply ContinuousLinearMap.opNorm_le_bound _ coefficientNonnegative
  intro field
  have high : ‖upper field.ofLp.2‖ ≤ coefficient * ‖field.ofLp.2‖ :=
    (upperBound _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) budgetNonnegative) (norm_nonneg _))
  have low : ‖lower field.ofLp.1‖ ≤ coefficient * ‖field.ofLp.1‖ :=
    (lowerBound _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) budgetNonnegative) (norm_nonneg _))
  have highSquare := pow_le_pow_left₀ (norm_nonneg _) high 2
  have lowSquare := pow_le_pow_left₀ (norm_nonneg _) low 2
  have sourceSquare := WithLp.prod_norm_sq_eq_of_L2 field
  have resultSquare := WithLp.prod_norm_sq_eq_of_L2 (hilbertOffDiagonal upper lower field)
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at sourceSquare
  change ‖hilbertOffDiagonal upper lower field‖ ^ 2 = ‖upper field.ofLp.2‖ ^ 2 +
    ‖lower field.ofLp.1‖ ^ 2 at resultSquare
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg coefficientNonnegative (norm_nonneg _))).mp
  calc
    ‖hilbertOffDiagonal upper lower field‖ ^ 2 ≤
        (coefficient * ‖field.ofLp.2‖) ^ 2 + (coefficient * ‖field.ofLp.1‖) ^ 2 := by
      rw [resultSquare]
      exact add_le_add highSquare lowSquare
    _ = coefficient ^ 2 * (‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2) := by ring
    _ = (coefficient * ‖field‖) ^ 2 := by rw [← sourceSquare]; ring

end HilbertProduct
end Grad.AnnularCoupledInverse
