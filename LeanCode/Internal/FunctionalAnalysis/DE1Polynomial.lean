import DE1Moments

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem polynomial_absolute_summable (polynomial : Polynomial ℝ) :
    Summable (fun index => |coefficient index * polynomial.eval (-node index)|) := by
  classical
  let majorant : ℕ → ℝ := fun index =>
    ∑ order ∈ polynomial.support,
      (|coefficient index| * node index ^ order) * |polynomial.coeff order|
  have termSummable (order : ℕ) : Summable (fun index =>
      (|coefficient index| * node index ^ order) * |polynomial.coeff order|) :=
    (coefficient_absolute_moment_summable order).mul_right _
  have majorantSummable : Summable majorant := by
    unfold majorant
    induction polynomial.support using Finset.induction_on with
    | empty => simp
    | @insert order orders fresh inductionHypothesis =>
        simp_rw [Finset.sum_insert fresh]
        exact (termSummable order).add inductionHypothesis
  apply majorantSummable.of_norm_bounded
  intro index
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  calc
    |coefficient index * polynomial.eval (-node index)| =
        |coefficient index *
          (∑ order ∈ polynomial.support, polynomial.coeff order * (-node index) ^ order)| := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ = |∑ order ∈ polynomial.support,
        coefficient index * (polynomial.coeff order * (-node index) ^ order)| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ order ∈ polynomial.support,
        |coefficient index * (polynomial.coeff order * (-node index) ^ order)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = majorant index := by
      unfold majorant
      apply Finset.sum_congr rfl
      intro order _membership
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (node_positive index)]
      ring

theorem polynomial_hasSum (polynomial : Polynomial ℝ) :
    HasSum (fun index => coefficient index * polynomial.eval (-node index)) (polynomial.eval 1) := by
  classical
  have termHasSum (order : ℕ) :
      HasSum (fun index => coefficient index *
        (polynomial.coeff order * (-node index) ^ order)) (polynomial.coeff order) := by
    have convergence := (infinite_moment_hasSum order).mul_left (polynomial.coeff order)
    have functionEquality :
        (fun index => polynomial.coeff order *
          (coefficient index * (-(2 : ℝ) ^ index) ^ order)) =
        (fun index => coefficient index *
          (polynomial.coeff order * (-node index) ^ order)) := by
      funext index
      unfold node
      ac_rfl
    rw [functionEquality] at convergence
    simpa only [mul_one] using convergence
  have finiteHasSum : ∀ orders : Finset ℕ,
      HasSum (fun index => ∑ order ∈ orders,
        coefficient index * (polynomial.coeff order * (-node index) ^ order))
        (∑ order ∈ orders, polynomial.coeff order) := by
    intro orders
    induction orders using Finset.induction_on with
    | empty => simp
    | @insert order orders fresh inductionHypothesis =>
        have convergence := (termHasSum order).add inductionHypothesis
        have functionEquality :
            (fun index => coefficient index *
                (polynomial.coeff order * (-node index) ^ order) +
              ∑ other ∈ orders, coefficient index *
                (polynomial.coeff other * (-node index) ^ other)) =
            (fun index => ∑ other ∈ insert order orders, coefficient index *
              (polynomial.coeff other * (-node index) ^ other)) := by
          funext index
          rw [Finset.sum_insert fresh]
        have sumEquality :
            polynomial.coeff order + ∑ other ∈ orders, polynomial.coeff other =
              ∑ other ∈ insert order orders, polynomial.coeff other := by
          rw [Finset.sum_insert fresh]
        rw [functionEquality, sumEquality] at convergence
        exact convergence
  have convergence := finiteHasSum polynomial.support
  have functionEquality :
      (fun index => ∑ order ∈ polynomial.support,
        coefficient index * (polynomial.coeff order * (-node index) ^ order)) =
      (fun index => coefficient index * polynomial.eval (-node index)) := by
    funext index
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  have sumEquality : (∑ order ∈ polynomial.support, polynomial.coeff order) =
      polynomial.eval 1 := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [one_pow, mul_one]
  rw [functionEquality, sumEquality] at convergence
  exact convergence

theorem polynomial_goal : PolynomialGoal := fun polynomial =>
  ⟨polynomial_absolute_summable polynomial, polynomial_hasSum polynomial⟩

end Grad.DiskExtension.Seeley
