import GC12Powers
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

/-- The exact scalar tail used in AP13 after the finitely many powers below
the grade have been separated. -/
def ap13ScalarMajorant (grade : ℕ) (thetaStar : ℝ) (power : ℕ) : ℝ :=
  (power : ℝ) ^ grade * thetaStar ^ (power - grade)

theorem ap13ScalarMajorant_summable (grade : ℕ) {thetaStar : ℝ}
    (thetaStarPositive : 0 < thetaStar) (thetaStarLt : thetaStar < 1) :
    Summable (ap13ScalarMajorant grade thetaStar) := by
  rw [← summable_nat_add_iff grade]
  have geometricPolynomial : Summable (fun power : ℕ =>
      ((power : ℝ) ^ grade) * thetaStar ^ power) := by
    exact summable_pow_mul_geometric_of_norm_lt_one grade
      (by simpa only [Real.norm_eq_abs, abs_of_pos thetaStarPositive] using thetaStarLt)
  have shiftedPolynomial : Summable (fun power : ℕ =>
      (((power + grade : ℕ) : ℝ) ^ grade) * thetaStar ^ power) := by
    have shiftedWithFactor : Summable (fun power : ℕ =>
        (((power + grade : ℕ) : ℝ) ^ grade) *
          thetaStar ^ (power + grade)) :=
      (summable_nat_add_iff grade).2 geometricPolynomial
    have scaled := shiftedWithFactor.mul_left (thetaStar ^ grade)⁻¹
    refine scaled.congr ?_
    intro power
    rw [pow_add]
    field_simp
  simpa only [ap13ScalarMajorant, Nat.add_sub_cancel_right] using shiftedPolynomial

theorem exists_ap13_thetaStar {theta : ℝ} (thetaNonnegative : 0 ≤ theta)
    (thetaLt : theta < 1) :
    ∃ thetaStar : ℝ, theta < thetaStar ∧ thetaStar < 1 ∧ 0 < thetaStar := by
  obtain ⟨thetaStar, thetaThetaStar, thetaStarLt⟩ := exists_between thetaLt
  exact ⟨thetaStar, thetaThetaStar, thetaStarLt,
    thetaNonnegative.trans_lt thetaThetaStar⟩

end Grad.GaugeCoefficients.Neumann.Regularity
