import SM1Interface

noncomputable section

open scoped BigOperators

namespace Grad.WeightedJets.SpatialMultiplier

theorem mem_below {order : ℕ} (upper lower : JetIndex order) :
    lower ∈ below upper ↔ indexLE lower upper := by
  classical
  simp [below]

def rectangleIndex {order : ℕ} (upper : JetIndex order)
    (first : Fin (upper.val.1 + 1)) (second : Fin (upper.val.2 + 1)) : JetIndex order :=
  ⟨(first.val, second.val),
    (Nat.add_le_add (Nat.le_of_lt_succ first.isLt) (Nat.le_of_lt_succ second.isLt)).trans upper.property⟩

theorem sum_below {Value : Type*} [AddCommMonoid Value] {order : ℕ}
    (upper : JetIndex order) (family : JetIndex order → Value) :
    (∑ lower ∈ below upper, family lower) =
      ∑ first : Fin (upper.val.1 + 1), ∑ second : Fin (upper.val.2 + 1),
        family (rectangleIndex upper first second) := by
  classical
  rw [← Fintype.sum_prod_type (fun pair : Fin (upper.val.1 + 1) × Fin (upper.val.2 + 1) =>
    family (rectangleIndex upper pair.1 pair.2))]
  refine Finset.sum_bij
    (fun lower membership =>
      (⟨lower.val.1, Nat.lt_succ_of_le ((mem_below upper lower).mp membership).1⟩,
       ⟨lower.val.2, Nat.lt_succ_of_le ((mem_below upper lower).mp membership).2⟩) :
      ∀ lower ∈ below upper, Fin (upper.val.1 + 1) × Fin (upper.val.2 + 1)) ?_ ?_ ?_ ?_
  · intro lower membership
    exact Finset.mem_univ _
  · intro first firstMem second secondMem equality
    apply Subtype.ext
    exact congrArg (fun pair : Fin (upper.val.1 + 1) × Fin (upper.val.2 + 1) =>
      (pair.1.val, pair.2.val)) equality
  · intro pair membership
    refine ⟨rectangleIndex upper pair.1 pair.2, ?_, ?_⟩
    · exact (mem_below _ _).mpr
        ⟨Nat.le_of_lt_succ pair.1.isLt, Nat.le_of_lt_succ pair.2.isLt⟩
    · rfl
  · intro lower membership
    rfl

theorem below_zero (order : ℕ) : below (zeroIndex order) = {zeroIndex order} := by
  classical
  ext lower
  rw [mem_below, Finset.mem_singleton]
  constructor
  · intro bound
    apply Subtype.ext
    apply Prod.ext <;> simp only [zeroIndex] at * <;> exact Nat.eq_zero_of_le_zero (by
      first | exact bound.1 | exact bound.2)
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

theorem below_self {order : ℕ} (index : JetIndex order) : index ∈ below index :=
  (mem_below _ _).mpr ⟨le_rfl, le_rfl⟩

theorem below_trans {order : ℕ} {first second third : JetIndex order}
    (firstMem : first ∈ below second) (secondMem : second ∈ below third) :
    first ∈ below third :=
  (mem_below _ _).mpr ⟨((mem_below _ _).mp firstMem).1.trans ((mem_below _ _).mp secondMem).1,
    ((mem_below _ _).mp firstMem).2.trans ((mem_below _ _).mp secondMem).2⟩

theorem sum_range_tail {Value : Type*} [AddCommMonoid Value]
    (upper lower : ℕ) (bound : lower ≤ upper) (family : ℕ → Value) :
    (∑ index ∈ Finset.range (upper + 1), if lower ≤ index then family index else 0) =
      ∑ index ∈ Finset.range (upper - lower + 1), family (lower + index) := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun index _ => index - lower) ?_ ?_ ?_ ?_
  · intro index membership
    simp only [Finset.mem_filter, Finset.mem_range] at membership ⊢
    omega
  · intro first firstMem second secondMem equality
    simp only [Finset.mem_filter, Finset.mem_range] at firstMem secondMem
    omega
  · intro index membership
    refine ⟨lower + index, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range] at membership ⊢
    omega
  · intro index membership
    simp only [Finset.mem_filter, Finset.mem_range] at membership
    congr 1
    omega

theorem alternating_choose (rank : ℕ) :
    (∑ index ∈ Finset.range (rank + 1), (-1 : ℝ) ^ index * rank.choose index) =
      if rank = 0 then 1 else 0 := by
  exact_mod_cast (Int.alternating_sum_range_choose (n := rank))

theorem alternating_choose_pair (upper retained : ℕ) :
    (∑ lower ∈ Finset.range (upper + 1), if retained ≤ lower then
      (-1 : ℝ) ^ lower * upper.choose lower * lower.choose retained else 0) =
      if retained = upper then (-1 : ℝ) ^ upper else 0 := by
  by_cases bound : retained ≤ upper
  · rw [sum_range_tail upper retained bound]
    calc
      _ = ((-1 : ℝ) ^ retained * upper.choose retained) *
          ∑ index ∈ Finset.range (upper - retained + 1),
            (-1 : ℝ) ^ index * (upper - retained).choose index := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index membership
        rw [mul_assoc, ← Nat.cast_mul, Nat.choose_mul (Nat.le_add_right retained index),
          Nat.add_sub_cancel_left, Nat.cast_mul, pow_add]
        ring
      _ = _ := by
        rw [alternating_choose]
        by_cases equality : retained = upper
        · subst retained
          simp
        · have nonzero : upper - retained ≠ 0 := by omega
          simp [equality, nonzero]
  · have different : retained ≠ upper := by omega
    rw [if_neg different]
    apply Finset.sum_eq_zero
    intro lower membership
    have outside : ¬ retained ≤ lower := by
      have := Finset.mem_range.mp membership
      omega
    exact if_neg outside

open Classical in
theorem binomial_cancellation (order : ℕ) (upper retained : JetIndex order) :
    (∑ lower ∈ below upper, if indexLE retained lower then
      (-1 : ℝ) ^ degree lower * binomial upper lower * binomial lower retained else 0) =
      if retained = upper then (-1 : ℝ) ^ degree upper else 0 := by
  classical
  rw [sum_below]
  have entry (first : Fin (upper.val.1 + 1)) (second : Fin (upper.val.2 + 1)) :
      (if indexLE retained (rectangleIndex upper first second) then
        (-1 : ℝ) ^ degree (rectangleIndex upper first second) *
          binomial upper (rectangleIndex upper first second) *
          binomial (rectangleIndex upper first second) retained else 0) =
      (if retained.val.1 ≤ first.val then
        (-1 : ℝ) ^ first.val * upper.val.1.choose first.val * first.val.choose retained.val.1 else 0) *
      (if retained.val.2 ≤ second.val then
        (-1 : ℝ) ^ second.val * upper.val.2.choose second.val * second.val.choose retained.val.2 else 0) := by
    simp only [indexLE, rectangleIndex, degree, binomial, Nat.cast_mul, pow_add]
    split_ifs <;> simp_all
    ring
  conv_lhs =>
    enter [2, first, 2, second]
    exact entry first second
  rw [← Finset.sum_mul_sum]
  erw [Fin.sum_univ_eq_sum_range (fun lower => if retained.val.1 ≤ lower then
      (-1 : ℝ) ^ lower * upper.val.1.choose lower * lower.choose retained.val.1 else 0),
    Fin.sum_univ_eq_sum_range (fun lower => if retained.val.2 ≤ lower then
      (-1 : ℝ) ^ lower * upper.val.2.choose lower * lower.choose retained.val.2 else 0),
    alternating_choose_pair, alternating_choose_pair]
  by_cases firstEq : retained.val.1 = upper.val.1
  · by_cases secondEq : retained.val.2 = upper.val.2
    · have equality : retained = upper := Subtype.ext (Prod.ext firstEq secondEq)
      simp [equality, degree, pow_add]
    · have different : retained ≠ upper := by
        intro equality
        exact secondEq (congrArg (fun index : JetIndex order => index.val.2) equality)
      simp [firstEq, secondEq, different]
  · have different : retained ≠ upper := by
      intro equality
      exact firstEq (congrArg (fun index : JetIndex order => index.val.1) equality)
    simp [firstEq, different]

end Grad.WeightedJets.SpatialMultiplier
