import MajorantExpBound

/-!
# NG_F06: summability of the N3 majorant

The factorial denominator dominates every polynomial factor: after the index
shift `p = q + j` the majorant is `‖I‖ K^j (K R)^q / q!` because
`p^{\underline j} / p! = 1 / (p - j)!`, and `Σ_q x^q / q!` converges for every
real `x`.
-/

noncomputable section

open scoped BigOperators

namespace Grad.CoefficientMajorants

open Grad.GaugeCoefficients.Algebra

/-- The shifted majorant: `‖I‖ K^{order} (K R)^q / q!`. -/
theorem expOperatorMajorant_shift (grade : ℕ) (identityNorm radius : ℝ) (order q : ℕ) :
    expOperatorMajorant grade identityNorm radius order (q + order) =
      identityNorm * gradeProductConstant grade ^ order *
        ((gradeProductConstant grade * radius) ^ q / (q.factorial : ℝ)) := by
  unfold expOperatorMajorant
  have factorial := Nat.factorial_mul_descFactorial (show order ≤ q + order by omega)
  rw [Nat.add_sub_cancel] at factorial
  have factorialPos : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos q
  have descEq : (((q + order).descFactorial order : ℕ) : ℝ) / (((q + order).factorial : ℕ) : ℝ) =
      1 / (q.factorial : ℝ) := by
    rw [← factorial, Nat.cast_mul]
    have descPos : (0 : ℝ) < (((q + order).descFactorial order : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr (by omega : order ≤ q + order)
    field_simp
  rw [descEq, Nat.add_sub_cancel, mul_pow, pow_add]
  ring

/-- The N3 majorant is summable for every generator radius. -/
theorem expOperatorMajorant_summable (grade : ℕ) (identityNorm radius : ℝ) (order : ℕ) :
    Summable (expOperatorMajorant grade identityNorm radius order) := by
  rw [← summable_nat_add_iff order]
  simp_rw [expOperatorMajorant_shift]
  exact (Real.summable_pow_div_factorial _).mul_left _

end Grad.CoefficientMajorants
