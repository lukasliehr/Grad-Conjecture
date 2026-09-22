import MajorantRootBound

/-!
# NG_F06: summability of the Q8 majorant

Separate the finite terms `p ≤ j` (they are the terms before the index shift
`p = q + j + 1`), then dominate the tail by a fixed polynomial in `q` times
`θ'^q` using `|c_p| ≤ 1` and `p^{\underline j} ≤ p^j`, and sum the
polynomial–geometric series for `0 ≤ θ' < 1` (binomial expansion of
`(q + a)^k` into Mathlib's `n^m r^n` series).
-/

noncomputable section

open scoped BigOperators

namespace Grad.CoefficientMajorants

open Grad.NonlinearQuotientBounds Grad.CartesianState

/-- Polynomial–geometric summability with a shifted polynomial base, for every
ratio `0 ≤ r < 1` (including `r = 0`). -/
theorem summable_add_pow_mul_geometric (k a : ℕ) {r : ℝ} (rNonneg : 0 ≤ r) (rLt : r < 1) :
    Summable (fun q : ℕ => ((q + a : ℕ) : ℝ) ^ k * r ^ q) := by
  have base : ∀ m : ℕ, Summable (fun q : ℕ => (q : ℝ) ^ m * r ^ q) := fun m =>
    summable_pow_mul_geometric_of_norm_lt_one m
      (by rw [Real.norm_eq_abs, abs_of_nonneg rNonneg]; exact rLt)
  have expand : ∀ q : ℕ, ((q + a : ℕ) : ℝ) ^ k * r ^ q =
      ∑ m ∈ Finset.range (k + 1),
        ((a : ℝ) ^ (k - m) * (k.choose m : ℝ)) * ((q : ℝ) ^ m * r ^ q) := by
    intro q
    rw [Nat.cast_add, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp_rw [expand]
  exact summable_sum fun m _ => (base m).mul_left _

theorem rootOperatorMajorant_nonneg (parameters : PhaseParameters) (grade order : ℕ)
    {theta radius : ℝ} (thetaNonneg : 0 ≤ theta) (radiusNonneg : 0 ≤ radius) (p : ℕ) :
    0 ≤ rootOperatorMajorant parameters grade order theta radius p := by
  unfold rootOperatorMajorant
  have : 0 ≤ radius + 1 := by linarith
  positivity

/-- The shifted majorant at `p = q + (order + 1)`: both ball factors are
`θ'^q` and `θ'^{q+1}`. -/
theorem rootOperatorMajorant_shift (parameters : PhaseParameters) (grade order : ℕ)
    (theta radius : ℝ) (q : ℕ) :
    rootOperatorMajorant parameters grade order theta radius (q + (order + 1)) =
      |rootCoefficient (q + (order + 1))| * ((q + (order + 1)).descFactorial order : ℝ) *
        ((2 : ℝ) ^ grade * Real.exp parameters.sigma0 ^ 2 *
          (((q + 2 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ q +
            ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ (q + 1))) := by
  unfold rootOperatorMajorant
  have first : q + (order + 1) - order = q + 1 := by omega
  simp only [first, Nat.add_sub_cancel, Nat.add_assoc]

/-- The Q8 majorant is summable on every ball `θ' < 1`. -/
theorem rootOperatorMajorant_summable (parameters : PhaseParameters) (grade order : ℕ)
    {theta radius : ℝ} (thetaNonneg : 0 ≤ theta) (thetaLt : theta < 1)
    (radiusNonneg : 0 ≤ radius) :
    Summable (rootOperatorMajorant parameters grade order theta radius) := by
  rw [← summable_nat_add_iff (order + 1)]
  set K : ℝ := (2 : ℝ) ^ grade * Real.exp parameters.sigma0 ^ 2 with K_def
  have KNonneg : 0 ≤ K := by positivity
  have radiusOne : 0 ≤ radius + 1 := by linarith
  -- the comparison series
  have firstSummable : Summable (fun q : ℕ =>
      K * (radius + 1) * (((q + (order + 2) : ℕ) : ℝ) ^ (order + grade + 1) * theta ^ q)) :=
    (summable_add_pow_mul_geometric (order + grade + 1) (order + 2) thetaNonneg thetaLt).mul_left _
  have secondSummable : Summable (fun q : ℕ =>
      K * (((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta) *
        (((q + (order + 1) : ℕ) : ℝ) ^ order * theta ^ q)) :=
    (summable_add_pow_mul_geometric order (order + 1) thetaNonneg thetaLt).mul_left _
  apply Summable.of_nonneg_of_le
    (fun q => rootOperatorMajorant_nonneg parameters grade order thetaNonneg radiusNonneg _)
    (fun q => ?_) (firstSummable.add secondSummable)
  rw [rootOperatorMajorant_shift]
  have coefficientLe : |rootCoefficient (q + (order + 1))| ≤ 1 := abs_rootCoefficient_le_one _
  have descLe : (((q + (order + 1)).descFactorial order : ℕ) : ℝ) ≤
      ((q + (order + 1) : ℕ) : ℝ) ^ order := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have thetaPow : 0 ≤ theta ^ q := pow_nonneg thetaNonneg q
  have bracketNonneg : 0 ≤ ((q + 2 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ q +
      ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ (q + 1) := by positivity
  have polyLe : ((q + (order + 1) : ℕ) : ℝ) ^ order * ((q + 2 : ℕ) : ℝ) ^ (grade + 1) ≤
      ((q + (order + 2) : ℕ) : ℝ) ^ (order + grade + 1) := by
    have firstLe : ((q + (order + 1) : ℕ) : ℝ) ^ order ≤ ((q + (order + 2) : ℕ) : ℝ) ^ order :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : q + (order + 1) ≤ q + (order + 2))) _
    have secondLe : ((q + 2 : ℕ) : ℝ) ^ (grade + 1) ≤ ((q + (order + 2) : ℕ) : ℝ) ^ (grade + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : q + 2 ≤ q + (order + 2))) _
    calc ((q + (order + 1) : ℕ) : ℝ) ^ order * ((q + 2 : ℕ) : ℝ) ^ (grade + 1)
        ≤ ((q + (order + 2) : ℕ) : ℝ) ^ order * ((q + (order + 2) : ℕ) : ℝ) ^ (grade + 1) :=
          mul_le_mul firstLe secondLe (pow_nonneg (Nat.cast_nonneg _) _)
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [← pow_add, Nat.add_assoc]
  calc |rootCoefficient (q + (order + 1))| * ((q + (order + 1)).descFactorial order : ℝ) *
        (K * (((q + 2 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ q +
          ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ (q + 1)))
      ≤ 1 * ((q + (order + 1) : ℕ) : ℝ) ^ order *
        (K * (((q + 2 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ q +
          ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ (q + 1))) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg KNonneg bracketNonneg)
        exact mul_le_mul coefficientLe descLe (Nat.cast_nonneg _) zero_le_one
    _ = K * (radius + 1) *
          ((((q + (order + 1) : ℕ) : ℝ) ^ order * ((q + 2 : ℕ) : ℝ) ^ (grade + 1)) * theta ^ q) +
        K * (((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta) *
          (((q + (order + 1) : ℕ) : ℝ) ^ order * theta ^ q) := by
        rw [pow_succ]
        ring
    _ ≤ K * (radius + 1) * (((q + (order + 2) : ℕ) : ℝ) ^ (order + grade + 1) * theta ^ q) +
        K * (((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta) *
          (((q + (order + 1) : ℕ) : ℝ) ^ order * theta ^ q) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right polyLe thetaPow)
            (mul_nonneg KNonneg radiusOne)) le_rfl

end Grad.CoefficientMajorants
