import TameRootSeries

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

/-! The scalar square-root series `F(t) = Σ_p c_p t^p` of Q8 on the real
unit interval: absolute convergence for `|t| < 1`, the identity
`F(t)² = 1 - t`, the closeness `|F(t) - 1| ≤ |t|/(1-|t|) ≤ 1/7` for
`|t| ≤ 1/8`, positivity there, and the identification with the positive
square root.

The identity `F² = 1 - t` is proved through the Cauchy product of the
series with itself: the Q7 recursion `(p+1) c_{p+1} = (p - 1/2) c_p` is the
coefficient form of the scalar differential equation `(1-t)F' = -F/2`, and
it forces the product coefficients `d_n = Σ_{p+q=n} c_p c_q` to satisfy
`(n+1) d_{n+1} = (n-1) d_n`, the coefficient form of `(1-t)(F²)' = -F²`,
i.e. of `d/dt (F²/(1-t)) = 0`; with `d_0 = 1` this gives `d_1 = -1` and
`d_n = 0` for `n ≥ 2`. -/

/-- The scalar root series `F(t) = Σ_p c_p t^p`. -/
def rootScalar (t : ℝ) : ℝ := ∑' p, rootCoefficient p * t ^ p

theorem rootScalar_term_norm_le (t : ℝ) (p : ℕ) :
    ‖rootCoefficient p * t ^ p‖ ≤ |t| ^ p := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |rootCoefficient p| * |t| ^ p ≤ 1 * |t| ^ p :=
        mul_le_mul_of_nonneg_right (abs_rootCoefficient_le_one p)
          (pow_nonneg (abs_nonneg t) p)
    _ = |t| ^ p := one_mul _

theorem rootScalar_norm_summable {t : ℝ} (small : |t| < 1) :
    Summable (fun p => ‖rootCoefficient p * t ^ p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (rootScalar_term_norm_le t)
    (summable_geometric_of_lt_one (abs_nonneg t) small)

theorem rootScalar_summable {t : ℝ} (small : |t| < 1) :
    Summable (fun p => rootCoefficient p * t ^ p) :=
  Summable.of_norm (rootScalar_norm_summable small)

theorem rootScalar_hasSum {t : ℝ} (small : |t| < 1) :
    HasSum (fun p => rootCoefficient p * t ^ p) (rootScalar t) :=
  (rootScalar_summable small).hasSum

/-! ### The Cauchy product coefficients -/

/-- The product coefficients `d_n = Σ_{p+q=n} c_p c_q` of `F²`. -/
def rootProductCoefficient (n : ℕ) : ℝ :=
  ∑ pair ∈ Finset.antidiagonal n, rootCoefficient pair.1 * rootCoefficient pair.2

/-- The weighted product coefficients `Σ_{p+q=n} p c_p c_q`. -/
def rootWeightedCoefficient (n : ℕ) : ℝ :=
  ∑ pair ∈ Finset.antidiagonal n,
    (pair.1 : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2)

/-- The weight may sit on either factor: `2 Σ p c_p c_q = n d_n`. -/
theorem two_rootWeightedCoefficient (n : ℕ) :
    2 * rootWeightedCoefficient n = (n : ℝ) * rootProductCoefficient n := by
  have swapped : rootWeightedCoefficient n = ∑ pair ∈ Finset.antidiagonal n,
      (pair.2 : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2) := by
    rw [rootWeightedCoefficient, ← Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun pair : ℕ × ℕ =>
        (pair.2 : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2))]
    apply Finset.sum_congr rfl
    intro pair _
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have split : rootWeightedCoefficient n + rootWeightedCoefficient n =
      ∑ pair ∈ Finset.antidiagonal n, ((pair.1 : ℝ) + (pair.2 : ℝ)) *
        (rootCoefficient pair.1 * rootCoefficient pair.2) := by
    rw [Finset.sum_congr rfl (fun (pair : ℕ × ℕ) _ => add_mul (pair.1 : ℝ) (pair.2 : ℝ)
      (rootCoefficient pair.1 * rootCoefficient pair.2)), Finset.sum_add_distrib, ← swapped]
    rfl
  have weight : ∀ pair ∈ Finset.antidiagonal n, ((pair.1 : ℝ) + (pair.2 : ℝ)) *
      (rootCoefficient pair.1 * rootCoefficient pair.2) =
      (n : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2) := by
    intro pair membership
    rw [Finset.mem_antidiagonal] at membership
    rw [← membership, Nat.cast_add]
  calc 2 * rootWeightedCoefficient n
      = rootWeightedCoefficient n + rootWeightedCoefficient n := two_mul _
    _ = ∑ pair ∈ Finset.antidiagonal n, ((pair.1 : ℝ) + (pair.2 : ℝ)) *
          (rootCoefficient pair.1 * rootCoefficient pair.2) := split
    _ = ∑ pair ∈ Finset.antidiagonal n,
          (n : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2) :=
        Finset.sum_congr rfl weight
    _ = (n : ℝ) * rootProductCoefficient n := by
        rw [rootProductCoefficient, Finset.mul_sum]

/-- The Q7 recursion in product form: `(p+1) c_{p+1} = (p - 1/2) c_p`. -/
theorem rootCoefficient_succ_mul (p : ℕ) :
    ((p : ℝ) + 1) * rootCoefficient (p + 1) = ((p : ℝ) - 1 / 2) * rootCoefficient p := by
  rw [rootCoefficient]
  have denominator_ne : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The recursion pushes the weight down one index:
`Σ_{p+q=n+1} p c_p c_q = Σ_{p+q=n} (p - 1/2) c_p c_q`. -/
theorem rootWeightedCoefficient_succ (n : ℕ) :
    rootWeightedCoefficient (n + 1) =
      rootWeightedCoefficient n - rootProductCoefficient n / 2 := by
  have step : ∀ pair ∈ Finset.antidiagonal n,
      ((pair.1 + 1 : ℕ) : ℝ) * (rootCoefficient (pair.1 + 1) * rootCoefficient pair.2) =
      (pair.1 : ℝ) * (rootCoefficient pair.1 * rootCoefficient pair.2) -
        rootCoefficient pair.1 * rootCoefficient pair.2 / 2 := by
    intro pair _
    have recursion := rootCoefficient_succ_mul pair.1
    push_cast
    calc ((pair.1 : ℝ) + 1) * (rootCoefficient (pair.1 + 1) * rootCoefficient pair.2)
        = (((pair.1 : ℝ) + 1) * rootCoefficient (pair.1 + 1)) * rootCoefficient pair.2 := by
          ring
      _ = (((pair.1 : ℝ) - 1 / 2) * rootCoefficient pair.1) * rootCoefficient pair.2 := by
          rw [recursion]
      _ = _ := by ring
  rw [rootWeightedCoefficient, Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib, rootWeightedCoefficient,
    rootProductCoefficient, Finset.sum_div]

/-- The product-coefficient recursion `(n+1) d_{n+1} = (n-1) d_n`: the
coefficient form of `(1-t)(F²)' = -F²`. -/
theorem rootProductCoefficient_succ (n : ℕ) :
    ((n : ℝ) + 1) * rootProductCoefficient (n + 1) =
      ((n : ℝ) - 1) * rootProductCoefficient n := by
  have first := two_rootWeightedCoefficient (n + 1)
  have second := two_rootWeightedCoefficient n
  have shift := rootWeightedCoefficient_succ n
  push_cast at first
  linear_combination (-1 : ℝ) * first + (2 : ℝ) * shift + second

theorem rootProductCoefficient_zero : rootProductCoefficient 0 = 1 := by
  rw [rootProductCoefficient, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    rootCoefficient, mul_one]

theorem rootProductCoefficient_one : rootProductCoefficient 1 = -1 := by
  have step := rootProductCoefficient_succ 0
  rw [rootProductCoefficient_zero] at step
  norm_num at step
  linarith

theorem rootProductCoefficient_add_two : ∀ k : ℕ, rootProductCoefficient (k + 2) = 0
  | 0 => by
    have index : 0 + 2 = 1 + 1 := by omega
    rw [index]
    have step := rootProductCoefficient_succ 1
    have zero_right : (((1 : ℕ) : ℝ) - 1) * rootProductCoefficient 1 = 0 := by
      rw [Nat.cast_one, sub_self, zero_mul]
    rw [zero_right] at step
    have pos : (0 : ℝ) < ((1 : ℕ) : ℝ) + 1 := by positivity
    exact (mul_eq_zero.mp step).resolve_left pos.ne'
  | k + 1 => by
    have index : k + 1 + 2 = k + 2 + 1 := by omega
    rw [index]
    have step := rootProductCoefficient_succ (k + 2)
    rw [rootProductCoefficient_add_two k, mul_zero] at step
    have pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) + 1 := by positivity
    exact (mul_eq_zero.mp step).resolve_left pos.ne'

theorem rootProductCoefficient_eq_zero {n : ℕ} (two_le : 2 ≤ n) :
    rootProductCoefficient n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest two_le
  rw [add_comm]
  exact rootProductCoefficient_add_two k

/-! ### The identity `F(t)² = 1 - t` -/

/-- `F(t)² = 1 - t` for `|t| < 1`. -/
theorem rootScalar_sq {t : ℝ} (small : |t| < 1) : rootScalar t ^ 2 = 1 - t := by
  have normSummable := rootScalar_norm_summable small
  have product :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm normSummable normSummable
  have collapse : ∀ n, (∑ pair ∈ Finset.antidiagonal n,
      (rootCoefficient pair.1 * t ^ pair.1) * (rootCoefficient pair.2 * t ^ pair.2)) =
      rootProductCoefficient n * t ^ n := by
    intro n
    rw [rootProductCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro pair membership
    rw [Finset.mem_antidiagonal] at membership
    rw [← membership, pow_add]
    ring
  have vanish : ∀ n ∉ Finset.range 2, rootProductCoefficient n * t ^ n = 0 := by
    intro n outside
    rw [Finset.mem_range, not_lt] at outside
    rw [rootProductCoefficient_eq_zero outside, zero_mul]
  rw [sq, rootScalar, product, tsum_congr collapse,
    (hasSum_sum_of_ne_finset_zero vanish).tsum_eq, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, rootProductCoefficient_zero,
    rootProductCoefficient_one]
  ring

/-! ### Closeness to one, positivity, and the positive root -/

/-- `|F(t) - 1| ≤ |t| / (1 - |t|)` for `|t| < 1`. -/
theorem rootScalar_sub_one_le {t : ℝ} (small : |t| < 1) :
    |rootScalar t - 1| ≤ |t| / (1 - |t|) := by
  have tail : rootScalar t - 1 = ∑' p, rootCoefficient (p + 1) * t ^ (p + 1) := by
    rw [rootScalar, (rootScalar_summable small).tsum_eq_zero_add, rootCoefficient, pow_zero,
      mul_one, add_sub_cancel_left]
  have tailNorm : Summable (fun p => ‖rootCoefficient (p + 1) * t ^ (p + 1)‖) :=
    (summable_nat_add_iff 1).mpr (rootScalar_norm_summable small)
  have geometricTail : Summable (fun p : ℕ => |t| ^ (p + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (abs_nonneg t) small)
  rw [tail]
  calc |∑' p, rootCoefficient (p + 1) * t ^ (p + 1)|
      = ‖∑' p, rootCoefficient (p + 1) * t ^ (p + 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' p, ‖rootCoefficient (p + 1) * t ^ (p + 1)‖ := norm_tsum_le_tsum_norm tailNorm
    _ ≤ ∑' p, |t| ^ (p + 1) :=
        tailNorm.tsum_le_tsum (fun p => rootScalar_term_norm_le t (p + 1)) geometricTail
    _ = |t| * ∑' p, |t| ^ p := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun p => by rw [pow_succ'])
    _ = |t| / (1 - |t|) := by
        rw [tsum_geometric_of_lt_one (abs_nonneg t) small, div_eq_mul_inv]

/-- `|F(t) - 1| ≤ 1/7` for `|t| ≤ 1/8`. -/
theorem rootScalar_sub_one_le_seventh {t : ℝ} (small : |t| ≤ 1 / 8) :
    |rootScalar t - 1| ≤ 1 / 7 := by
  have lt_one : |t| < 1 := lt_of_le_of_lt small (by norm_num)
  apply (rootScalar_sub_one_le lt_one).trans
  have denominator_pos : (0 : ℝ) < 1 - |t| := by linarith
  rw [div_le_iff₀ denominator_pos]
  linarith

/-- `F(t) > 0` for `|t| ≤ 1/8`. -/
theorem rootScalar_pos {t : ℝ} (small : |t| ≤ 1 / 8) : 0 < rootScalar t := by
  have close := rootScalar_sub_one_le_seventh small
  have lower := (abs_le.mp close).1
  linarith

/-- `F(t)` is the positive square root of `1 - t` for `|t| ≤ 1/8`. -/
theorem rootScalar_eq_sqrt {t : ℝ} (small : |t| ≤ 1 / 8) :
    rootScalar t = Real.sqrt (1 - t) := by
  have lt_one : |t| < 1 := lt_of_le_of_lt small (by norm_num)
  rw [← rootScalar_sq lt_one, Real.sqrt_sq (rootScalar_pos small).le]

/-- The complex series with the real coefficients at a real point is the
real series. -/
theorem rootScalar_hasSum_complex {t : ℝ} (small : |t| < 1) :
    HasSum (fun p => ((rootCoefficient p : ℝ) : ℂ) * ((t : ℂ)) ^ p)
      ((rootScalar t : ℝ) : ℂ) := by
  have cast := Complex.hasSum_ofReal.mpr (rootScalar_hasSum small)
  have fun_eq : (fun p => ((rootCoefficient p * t ^ p : ℝ) : ℂ)) =
      fun p => ((rootCoefficient p : ℝ) : ℂ) * ((t : ℂ)) ^ p := by
    funext p
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [fun_eq] at cast
  exact cast

end Grad.NonlinearQuotientBounds
