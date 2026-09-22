import TameSeriesAlgebra

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The quadratic-curve expansion of ring powers in the coefficient core:
the literal curve `x + t u + t² w`, its working radius, the exact binomial
expansion of its powers, and the second-order Taylor remainder with its
quadratic-in-`t` graded envelope majorant.  These are the convergent root
Taylor remainders behind the Q15/Q20 tower and Q24. -/

variable {parameters : PhaseParameters}

/-- The quadratic curve through `x` with velocity `u` and curvature `w`. -/
def rootCurvePoint (x u w : TameCoefficient parameters) (t : ℝ) :
    TameCoefficient parameters :=
  x + (t : ℂ) • u + ((t : ℂ)) ^ 2 • w

theorem rootCurvePoint_zero (x u w : TameCoefficient parameters) :
    rootCurvePoint x u w 0 = x := by
  rw [rootCurvePoint, Complex.ofReal_zero, zero_smul, add_zero,
    zero_pow (by norm_num), zero_smul, add_zero]

theorem rootCurvePoint_envelope_le (x u w : TameCoefficient parameters) (grade : ℕ) (t : ℝ) :
    coefficientEnvelope grade (rootCurvePoint x u w t) ≤
      coefficientEnvelope grade x + |t| * coefficientEnvelope grade u +
        |t| ^ 2 * coefficientEnvelope grade w := by
  calc coefficientEnvelope grade (rootCurvePoint x u w t)
      ≤ coefficientEnvelope grade (x + (t : ℂ) • u) +
          coefficientEnvelope grade (((t : ℂ)) ^ 2 • w) :=
        coefficientEnvelope_add_le grade _ _
    _ ≤ coefficientEnvelope grade x + coefficientEnvelope grade ((t : ℂ) • u) +
          coefficientEnvelope grade (((t : ℂ)) ^ 2 • w) :=
        add_le_add (coefficientEnvelope_add_le grade _ _) le_rfl
    _ = _ := by
        rw [coefficientEnvelope_smul, coefficientEnvelope_smul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs]

/-- The padded direction sizes. -/
def rootDirectionSize (u : TameCoefficient parameters) : ℝ :=
  coefficientEnvelope 0 u + 1

theorem rootDirectionSize_one_le (u : TameCoefficient parameters) :
    1 ≤ rootDirectionSize u := by
  have := coefficientEnvelope_nonneg 0 u
  rw [rootDirectionSize]
  linarith

theorem rootDirectionSize_pos (u : TameCoefficient parameters) :
    0 < rootDirectionSize u :=
  lt_of_lt_of_le zero_lt_one (rootDirectionSize_one_le u)

theorem envelope_le_rootDirectionSize (u : TameCoefficient parameters) :
    coefficientEnvelope 0 u ≤ rootDirectionSize u := by
  rw [rootDirectionSize]
  linarith

/-- The working curve radius: inside it the curve stays strictly inside the
unit grade-zero ball and the padded collapse ratio stays below one. -/
def rootCurveRadius (x u w : TameCoefficient parameters) : ℝ :=
  min 1 ((1 - rootSmallRadius x) /
    (2 * (1 + rootDirectionSize u + rootDirectionSize w)))

theorem rootCurveRadius_pos {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    0 < rootCurveRadius x u w := by
  apply lt_min zero_lt_one
  apply div_pos
  · have := rootSmallRadius_lt_one small
    linarith
  · have := rootDirectionSize_pos u
    have := rootDirectionSize_pos w
    linarith

theorem rootCurveRadius_le_one (x u w : TameCoefficient parameters) :
    rootCurveRadius x u w ≤ 1 := min_le_left _ _

theorem rootCurveRadius_nonneg {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    0 ≤ rootCurveRadius x u w := (rootCurveRadius_pos small u w).le

/-- The padded direction budget of the radius. -/
theorem rootCurveRadius_directions_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    rootCurveRadius x u w * (rootDirectionSize u + rootDirectionSize w) ≤
      (1 - rootSmallRadius x) / 2 := by
  have sizes_pos : (0 : ℝ) < 1 + rootDirectionSize u + rootDirectionSize w := by
    have := rootDirectionSize_pos u
    have := rootDirectionSize_pos w
    linarith
  have radius_le := min_le_right 1 ((1 - rootSmallRadius x) /
    (2 * (1 + rootDirectionSize u + rootDirectionSize w)))
  have numerator_nonneg : 0 ≤ 1 - rootSmallRadius x := by
    have := rootSmallRadius_lt_one small
    linarith
  have sizes_nonneg : 0 ≤ rootDirectionSize u + rootDirectionSize w := by
    have := rootDirectionSize_pos u
    have := rootDirectionSize_pos w
    linarith
  calc rootCurveRadius x u w * (rootDirectionSize u + rootDirectionSize w)
      ≤ ((1 - rootSmallRadius x) /
          (2 * (1 + rootDirectionSize u + rootDirectionSize w))) *
        (rootDirectionSize u + rootDirectionSize w) :=
        mul_le_mul_of_nonneg_right radius_le sizes_nonneg
    _ ≤ (1 - rootSmallRadius x) / 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith)).mpr
        have clear : (1 - rootSmallRadius x) / 2 *
            (2 * (1 + rootDirectionSize u + rootDirectionSize w)) =
            (1 - rootSmallRadius x) * (1 + rootDirectionSize u + rootDirectionSize w) := by
          ring
        rw [clear]
        nlinarith

/-- The collapse ratio of the remainder majorant. -/
def rootCollapseRatio (x : TameCoefficient parameters) : ℝ :=
  (1 + rootSmallRadius x) / 2

theorem rootCollapseRatio_lt_one {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) : rootCollapseRatio x < 1 := by
  have := rootSmallRadius_lt_one small
  rw [rootCollapseRatio]
  linarith

theorem rootSmallRadius_half_le (x : TameCoefficient parameters) :
    (1 / 2 : ℝ) ≤ rootSmallRadius x := by
  have := coefficientEnvelope_nonneg 0 x
  rw [rootSmallRadius]
  linarith

theorem rootCollapseRatio_half_le (x : TameCoefficient parameters) :
    (1 / 2 : ℝ) ≤ rootCollapseRatio x := by
  have := rootSmallRadius_half_le x
  rw [rootCollapseRatio]
  linarith

theorem rootCollapseRatio_pos (x : TameCoefficient parameters) :
    0 < rootCollapseRatio x :=
  lt_of_lt_of_le (by norm_num) (rootCollapseRatio_half_le x)

theorem rootSmallRadius_le_collapse {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) :
    rootSmallRadius x ≤ rootCollapseRatio x := by
  have := rootSmallRadius_lt_one small
  rw [rootCollapseRatio]
  linarith

/-- The collapsed base bound inside the radius. -/
theorem rootCurve_collapse_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    {t : ℝ} (inside : |t| ≤ rootCurveRadius x u w) :
    rootSmallRadius x + (|t| * rootDirectionSize u + |t| ^ 2 * rootDirectionSize w) ≤
      rootCollapseRatio x := by
  have abs_nonneg_t : 0 ≤ |t| := abs_nonneg t
  have radius_le_one := rootCurveRadius_le_one x u w
  have t_le_one : |t| ≤ 1 := inside.trans radius_le_one
  have squared_le : |t| ^ 2 ≤ |t| := by
    calc |t| ^ 2 = |t| * |t| := by ring
    _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right t_le_one abs_nonneg_t
    _ = |t| := one_mul _
  have budget : |t| * (rootDirectionSize u + rootDirectionSize w) ≤
      (1 - rootSmallRadius x) / 2 := by
    have sizes_nonneg : 0 ≤ rootDirectionSize u + rootDirectionSize w := by
      have := rootDirectionSize_pos u
      have := rootDirectionSize_pos w
      linarith
    exact (mul_le_mul_of_nonneg_right inside sizes_nonneg).trans
      (rootCurveRadius_directions_le small u w)
  have w_term_le : |t| ^ 2 * rootDirectionSize w ≤ |t| * rootDirectionSize w :=
    mul_le_mul_of_nonneg_right squared_le (rootDirectionSize_pos w).le
  rw [rootCollapseRatio]
  have expand : |t| * rootDirectionSize u + |t| * rootDirectionSize w =
      |t| * (rootDirectionSize u + rootDirectionSize w) := by ring
  linarith [budget, w_term_le, expand ▸ le_refl
    (|t| * rootDirectionSize u + |t| * rootDirectionSize w)]

/-- Inside the curve radius the curve point stays strictly small. -/
theorem rootCurvePoint_lt_one {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    {t : ℝ} (inside : |t| ≤ rootCurveRadius x u w) :
    coefficientEnvelope 0 (rootCurvePoint x u w t) < 1 := by
  have point_le := rootCurvePoint_envelope_le x u w 0 t
  have base_le := envelope_le_rootSmallRadius small
  have u_le := envelope_le_rootDirectionSize u
  have w_le := envelope_le_rootDirectionSize w
  have collapse := rootCurve_collapse_le small u w inside
  have ratio_lt := rootCollapseRatio_lt_one small
  have abs_nonneg_t : 0 ≤ |t| := abs_nonneg t
  have sq_nonneg_t : 0 ≤ |t| ^ 2 := pow_nonneg abs_nonneg_t 2
  have u_term : |t| * coefficientEnvelope 0 u ≤ |t| * rootDirectionSize u :=
    mul_le_mul_of_nonneg_left u_le abs_nonneg_t
  have w_term : |t| ^ 2 * coefficientEnvelope 0 w ≤ |t| ^ 2 * rootDirectionSize w :=
    mul_le_mul_of_nonneg_left w_le sq_nonneg_t
  linarith

/-! ### Natural multiples in the ring -/

theorem tameMul_natCast (count : ℕ) (element : TameCoefficient parameters) :
    element * (count : TameCoefficient parameters) = ((count : ℕ) : ℂ) • element := by
  induction count with
  | zero =>
    rw [Nat.cast_zero, mul_zero, Nat.cast_zero, zero_smul]
  | succ smaller inductive_step =>
    rw [Nat.cast_succ, mul_add, mul_one, inductive_step, Nat.cast_succ, add_smul, one_smul]

/-! ### The exact curve-power expansion -/

/-- One decorated monomial of the curve expansion. -/
def rootCurveMonomial (x u w : TameCoefficient parameters) (t : ℝ)
    (power drop low : ℕ) : TameCoefficient parameters :=
  ((((power.choose drop) * (drop.choose low) : ℕ) : ℂ) *
      ((t : ℂ)) ^ (low + 2 * (drop - low))) •
    (x ^ (power - drop) * (u ^ low * w ^ (drop - low)))

/-- The binomial expansion of the quadratic tail power. -/
theorem rootCurveTail_pow (u w : TameCoefficient parameters) (t : ℝ) (drop : ℕ) :
    ((t : ℂ) • u + ((t : ℂ)) ^ 2 • w) ^ drop =
      ∑ low ∈ Finset.range (drop + 1),
        (((drop.choose low : ℕ) : ℂ) * ((t : ℂ)) ^ (low + 2 * (drop - low))) •
          (u ^ low * w ^ (drop - low)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro low _
  rw [smul_pow, smul_pow, smul_mul_smul_comm, tameMul_natCast, smul_smul]
  congr 1
  rw [← pow_mul, ← pow_add]

/-- The full curve-power expansion. -/
theorem rootCurvePoint_pow (x u w : TameCoefficient parameters) (t : ℝ) (power : ℕ) :
    (rootCurvePoint x u w t) ^ power =
      ∑ drop ∈ Finset.range (power + 1), ∑ low ∈ Finset.range (drop + 1),
        rootCurveMonomial x u w t power drop low := by
  have regroup : rootCurvePoint x u w t = x + ((t : ℂ) • u + ((t : ℂ)) ^ 2 • w) := by
    rw [rootCurvePoint, add_assoc]
  rw [regroup, add_pow]
  have reindex := Finset.sum_range_reflect (fun exponent =>
    x ^ exponent * ((t : ℂ) • u + ((t : ℂ)) ^ 2 • w) ^ (power - exponent) *
      ((power.choose exponent : ℕ) : TameCoefficient parameters)) (power + 1)
  rw [← reindex]
  apply Finset.sum_congr rfl
  intro drop membership
  have drop_le : drop ≤ power := Nat.lt_succ_iff.mp (Finset.mem_range.mp membership)
  have exponent_form : power + 1 - 1 - drop = power - drop := by omega
  have recover : power - (power - drop) = drop := by omega
  rw [exponent_form, recover, Nat.choose_symm drop_le, tameMul_natCast,
    rootCurveTail_pow u w t drop, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro low _
  rw [mul_smul_comm, smul_smul, rootCurveMonomial]
  congr 1
  rw [Nat.cast_mul]
  ring

/-! ### The Taylor remainder and its identity -/

/-- The exact second-order Taylor remainder of a positive curve power. -/
def rootCurveRemainder (x u w : TameCoefficient parameters) (t : ℝ) (q : ℕ) :
    TameCoefficient parameters :=
  (rootCurvePoint x u w t) ^ (q + 1) - x ^ (q + 1) -
    (((q + 1 : ℕ) : ℂ) * (t : ℂ)) • (x ^ q * u)

theorem rootCurveMonomial_zeroth (x u w : TameCoefficient parameters) (t : ℝ) (power : ℕ) :
    rootCurveMonomial x u w t power 0 0 = x ^ power := by
  rw [rootCurveMonomial]
  simp

theorem rootCurveMonomial_linear (x u w : TameCoefficient parameters) (t : ℝ) (q : ℕ) :
    rootCurveMonomial x u w t (q + 1) 1 1 =
      (((q + 1 : ℕ) : ℂ) * (t : ℂ)) • (x ^ q * u) := by
  rw [rootCurveMonomial]
  have exponent_one : 1 + 2 * (1 - 1) = 1 := by omega
  have drop_one : q + 1 - 1 = q := by omega
  rw [exponent_one, drop_one, Nat.choose_one_right, Nat.choose_self, pow_one]
  have tail_one : u ^ 1 * w ^ (1 - 1) = u := by
    rw [pow_one]
    have : (1 : ℕ) - 1 = 0 := by omega
    rw [this, pow_zero, mul_one]
  rw [tail_one]
  congr 2
  rw [Nat.mul_one]

/-- The remainder is exactly the quadratic part of the expansion. -/
theorem rootCurveRemainder_eq (x u w : TameCoefficient parameters) (t : ℝ) (q : ℕ) :
    rootCurveRemainder x u w t q =
      (∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
        rootCurveMonomial x u w t (q + 1) (inner + 2) low) +
      rootCurveMonomial x u w t (q + 1) 1 0 := by
  have expansion := rootCurvePoint_pow x u w t (q + 1)
  have outer_peel : (∑ drop ∈ Finset.range (q + 2), ∑ low ∈ Finset.range (drop + 1),
      rootCurveMonomial x u w t (q + 1) drop low) =
      (∑ drop ∈ Finset.range (q + 1), ∑ low ∈ Finset.range (drop + 2),
        rootCurveMonomial x u w t (q + 1) (drop + 1) low) +
      ∑ low ∈ Finset.range 1, rootCurveMonomial x u w t (q + 1) 0 low :=
    Finset.sum_range_succ' _ (q + 1)
  have second_peel : (∑ drop ∈ Finset.range (q + 1), ∑ low ∈ Finset.range (drop + 2),
      rootCurveMonomial x u w t (q + 1) (drop + 1) low) =
      (∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
        rootCurveMonomial x u w t (q + 1) (inner + 2) low) +
      ∑ low ∈ Finset.range 2, rootCurveMonomial x u w t (q + 1) 1 low :=
    Finset.sum_range_succ' _ q
  have zero_block : (∑ low ∈ Finset.range 1, rootCurveMonomial x u w t (q + 1) 0 low) =
      x ^ (q + 1) := by
    rw [Finset.sum_range_one, rootCurveMonomial_zeroth]
  have one_block : (∑ low ∈ Finset.range 2, rootCurveMonomial x u w t (q + 1) 1 low) =
      rootCurveMonomial x u w t (q + 1) 1 0 +
        (((q + 1 : ℕ) : ℂ) * (t : ℂ)) • (x ^ q * u) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, rootCurveMonomial_linear]
  rw [rootCurveRemainder, expansion, outer_peel, second_peel, zero_block, one_block]
  abel

end Grad.NonlinearQuotientBounds
