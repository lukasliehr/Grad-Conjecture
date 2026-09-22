import DE1Interface

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

@[simp] theorem node_zero : node 0 = 1 := rfl

theorem node_positive (index : ℕ) : 0 < node index := pow_pos (by norm_num) index

theorem node_one_le (index : ℕ) : 1 ≤ node index := one_le_pow₀ (by norm_num)

theorem node_strictMono : StrictMono node := pow_right_strictMono₀ (by norm_num)

theorem node_injective : Function.Injective node := node_strictMono.injective

theorem node_sub_ne_zero (first second : ℕ) (distinct : first ≠ second) :
    node first - node second ≠ 0 := sub_ne_zero.mpr (node_injective.ne distinct)

theorem node_succ (index : ℕ) : node (index + 1) = node index * 2 := pow_succ _ _

theorem node_add (first second : ℕ) : node (first + second) = node first * node second := pow_add _ _ _

theorem geometry_goal : GeometryGoal :=
  ⟨fun index => ⟨node_one_le index, node_positive index⟩, node_strictMono, node_sub_ne_zero⟩

theorem finite_zero_padding (cutoff index : ℕ) (outside : cutoff < index) :
    finiteCoefficient cutoff index = 0 := if_neg (not_le.mpr outside)

theorem finite_diagonal_formula (index : ℕ) :
    finiteCoefficient index index =
      ∏ other ∈ Finset.range index, (1 + node other) / (node other - node index) := by
  simp [finiteCoefficient, Finset.range_add_one]

theorem finite_diagonal_sign (index : ℕ) : 0 < (-1 : ℝ) ^ index * finiteCoefficient index index := by
  have positive : 0 < ∏ other ∈ Finset.range index,
      -((1 + node other) / (node other - node index)) := by
    apply Finset.prod_pos
    intro other membership
    exact neg_pos.mpr (div_neg_of_pos_of_neg (by linarith [node_positive other])
      (sub_neg.mpr (node_strictMono (Finset.mem_range.mp membership))))
  simpa only [Finset.prod_neg, Finset.card_range, ← finite_diagonal_formula] using positive

theorem finite_succ (cutoff index : ℕ) (retained : index ≤ cutoff) :
    finiteCoefficient (cutoff + 1) index = finiteCoefficient cutoff index *
      ((1 + node (cutoff + 1)) / (node (cutoff + 1) - node index)) := by
  have distinct : cutoff + 1 ≠ index := by omega
  have fresh : cutoff + 1 ∉ (Finset.range (cutoff + 1)).erase index := by simp
  simp only [finiteCoefficient, if_pos retained, if_pos (by omega : index ≤ cutoff + 1),
    Finset.range_add_one (n := cutoff + 1), Finset.erase_insert_of_ne distinct]
  rw [Finset.prod_insert fresh, mul_comm]

theorem finite_sign (cutoff index : ℕ) (retained : index ≤ cutoff) :
    0 < (-1 : ℝ) ^ index * finiteCoefficient cutoff index := by
  induction cutoff with
  | zero =>
      have equality : index = 0 := by omega
      subst index
      exact finite_diagonal_sign 0
  | succ cutoff inductionHypothesis =>
      by_cases previous : index ≤ cutoff
      · rw [finite_succ cutoff index previous, ← mul_assoc]
        exact mul_pos (inductionHypothesis previous)
          (div_pos (by linarith [node_positive (cutoff + 1)])
            (sub_pos.mpr (node_strictMono (by omega))))
      · have equality : index = cutoff + 1 := by omega
        subst index
        exact finite_diagonal_sign (cutoff + 1)

theorem finite_lagrange (cutoff index : ℕ) (retained : index ≤ cutoff) :
    finiteCoefficient cutoff index =
      (Lagrange.basis (Finset.range (cutoff + 1)) (fun other => -node other) index).eval 1 := by
  rw [finiteCoefficient, if_pos retained, Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro other _membership
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, sub_neg_eq_add]
  ring

theorem finite_goal : FiniteGoal :=
  ⟨finite_zero_padding, by simp [finiteCoefficient], finite_lagrange, finite_sign, finite_succ⟩

theorem finite_polynomial (cutoff : ℕ) (polynomial : Polynomial ℝ)
    (boundedDegree : polynomial.natDegree ≤ cutoff) :
    ∑ index ∈ Finset.range (cutoff + 1),
      finiteCoefficient cutoff index * polynomial.eval (-node index) = polynomial.eval 1 := by
  have injective : Set.InjOn (fun index : ℕ => -node index) (Finset.range (cutoff + 1)) :=
    fun _ _ _ _ equality => node_injective (neg_injective equality)
  have degreeBound : polynomial.degree < (Finset.range (cutoff + 1)).card := by
    apply lt_of_le_of_lt polynomial.degree_le_natDegree
    exact_mod_cast (show polynomial.natDegree < (Finset.range (cutoff + 1)).card from by
      simpa using (Nat.lt_succ_of_le boundedDegree))
  have interpolation := congrArg (Polynomial.eval (1 : ℝ)) (Lagrange.eq_interpolate injective degreeBound)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at interpolation
  refine Eq.trans ?_ interpolation.symm
  apply Finset.sum_congr rfl
  intro index membership
  rw [finite_lagrange cutoff index (by simpa using membership), Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem finite_moment (cutoff order : ℕ) (boundedOrder : order ≤ cutoff) :
    ∑ index ∈ Finset.range (cutoff + 1),
      finiteCoefficient cutoff index * (-node index) ^ order = 1 := by
  simpa using finite_polynomial cutoff ((Polynomial.X : Polynomial ℝ) ^ order) (by simpa using boundedOrder)

theorem finite_moment_goal : FiniteMomentGoal := ⟨finite_polynomial, finite_moment⟩

end Grad.DiskExtension.Seeley
