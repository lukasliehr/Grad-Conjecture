import SM1Calculus
import SM1Indices

noncomputable section

open Grad.PDEBootstrap
open Grad.WeakTesting.Commutation (differentiate listDerivative)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem repeatDerivative_sum {Index : Type*} (indices : Finset Index) (direction : Fin 2)
    (rank : ℕ) (family : Index → Spatial → ℝ)
    (smoothness : ∀ index ∈ indices, ContDiff ℝ ∞ (family index)) :
    repeatDerivative direction rank (fun point => ∑ index ∈ indices, family index point) =
      fun point => ∑ index ∈ indices, repeatDerivative direction rank (family index) point := by
  induction rank with
  | zero => rfl
  | succ rank induction =>
    rw [repeatDerivative_succ, induction, differentiate_sum _ _ _
      (fun index membership => repeatDerivative_smooth _ _ _ (smoothness index membership))]
    simp only [← repeatDerivative_succ]

theorem repeatDerivative_const_mul (direction : Fin 2) (rank : ℕ) (constant : ℝ)
    (scalar : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ scalar) :
    repeatDerivative direction rank (fun point => constant * scalar point) =
      fun point => constant * repeatDerivative direction rank scalar point := by
  induction rank with
  | zero => rfl
  | succ rank induction =>
    rw [repeatDerivative_succ, induction, differentiate_const_mul _ _ _
      (repeatDerivative_smooth direction rank scalar smoothness), ← repeatDerivative_succ]

theorem repeatDerivative_mul_right (direction : Fin 2) (rank : ℕ) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    repeatDerivative direction rank (fun point => first point * second point) =
      fun point => ∑ index ∈ Finset.range (rank + 1), (rank.choose index : ℝ) *
        (repeatDerivative direction (rank - index) first point *
          repeatDerivative direction index second point) := by
  have exchange : (fun point => first point * second point) =
      fun point => second point * first point := by
    funext point
    exact mul_comm _ _
  rw [exchange, repeatDerivative_mul direction rank second first secondSmooth firstSmooth]
  funext point
  apply Finset.sum_congr rfl
  intro index membership
  ring

theorem scalarDerivative_repeat (index : ℕ × ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    scalarDerivative index scalar =
      repeatDerivative 0 index.1 (repeatDerivative 1 index.2 scalar) := by
  rw [scalarDerivative_list index scalar smoothness, listDerivative_append]
  rfl

theorem scalarDerivative_mul_rectangle (zeros ones : ℕ) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    scalarDerivative (zeros, ones) (fun point => first point * second point) =
      fun point => ∑ firstIndex ∈ Finset.range (zeros + 1),
        ∑ secondIndex ∈ Finset.range (ones + 1),
          (zeros.choose firstIndex : ℝ) * (ones.choose secondIndex : ℝ) *
            scalarDerivative (zeros - firstIndex, ones - secondIndex) first point *
            scalarDerivative (firstIndex, secondIndex) second point := by
  rw [scalarDerivative_repeat _ _ (firstSmooth.mul secondSmooth),
    repeatDerivative_mul_right 1 ones first second firstSmooth secondSmooth,
    repeatDerivative_sum _ 0 zeros _ (by
      intro index membership
      exact contDiff_const.mul ((repeatDerivative_smooth 1 _ first firstSmooth).mul
        (repeatDerivative_smooth 1 _ second secondSmooth)))]
  simp_rw [repeatDerivative_const_mul 0 zeros _ _
      ((repeatDerivative_smooth 1 _ first firstSmooth).mul
        (repeatDerivative_smooth 1 _ second secondSmooth)),
    repeatDerivative_mul_right 0 zeros _ _
      (repeatDerivative_smooth 1 _ first firstSmooth)
      (repeatDerivative_smooth 1 _ second secondSmooth)]
  funext point
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstIndex firstMem
  apply Finset.sum_congr rfl
  intro secondIndex secondMem
  rw [scalarDerivative_repeat _ first firstSmooth,
    scalarDerivative_repeat _ second secondSmooth]
  ring

theorem sum_fin_rectangle {Value : Type*} [AddCommMonoid Value] (zeros ones : ℕ)
    (family : ℕ → ℕ → Value) :
    (∑ first : Fin (zeros + 1), ∑ second : Fin (ones + 1), family first.val second.val) =
      ∑ first ∈ Finset.range (zeros + 1), ∑ second ∈ Finset.range (ones + 1), family first second := by
  simp_rw [Fin.sum_univ_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun first =>
    ∑ second ∈ Finset.range (ones + 1), family first second) (zeros + 1)

theorem scalarDerivative_mul (order : ℕ) (upper : JetIndex order) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (point : Spatial) :
    scalarDerivative upper.val (fun point => first point * second point) point =
      ∑ lower ∈ below upper, (binomial upper lower : ℝ) *
        scalarDerivative (difference upper lower).val first point *
        scalarDerivative lower.val second point := by
  rw [sum_below, scalarDerivative_mul_rectangle upper.val.1 upper.val.2 first second firstSmooth secondSmooth]
  simp only [rectangleIndex, difference, binomial, Nat.cast_mul]
  exact (sum_fin_rectangle upper.val.1 upper.val.2 (fun firstIndex secondIndex =>
    (upper.val.1.choose firstIndex : ℝ) * (upper.val.2.choose secondIndex : ℝ) *
      scalarDerivative (upper.val.1 - firstIndex, upper.val.2 - secondIndex) first point *
      scalarDerivative (firstIndex, secondIndex) second point)).symm

theorem nested_difference_derivative {order : ℕ} (upper lower retained : JetIndex order)
    (lowerBound : indexLE lower upper) (retainedBound : indexLE retained lower)
    (scalar : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ scalar) :
    scalarDerivative (difference lower retained).val
        (scalarDerivative (difference upper lower).val scalar) =
      scalarDerivative (difference upper retained).val scalar := by
  rw [scalarDerivative_comp _ _ scalar smoothness]
  rcases lowerBound with ⟨lowerFirst, lowerSecond⟩
  rcases retainedBound with ⟨retainedFirst, retainedSecond⟩
  congr 1
  apply Prod.ext <;> dsimp [difference] <;> omega

theorem scalar_adjoint (order : ℕ) (upper : JetIndex order) (scalar test : Spatial → ℝ)
    (scalarSmooth : ContDiff ℝ ∞ scalar) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) :
    (∑ lower ∈ below upper, (-1 : ℝ) ^ degree lower * binomial upper lower *
      scalarDerivative lower.val
        (fun point => scalarDerivative (difference upper lower).val scalar point * test point) point) =
      (-1 : ℝ) ^ degree upper * scalar point * scalarDerivative upper.val test point := by
  classical
  calc
    _ = ∑ lower ∈ below upper, ∑ retained : JetIndex order,
        if indexLE retained lower then
          ((-1 : ℝ) ^ degree lower * binomial upper lower * binomial lower retained) *
            scalarDerivative (difference upper retained).val scalar point *
            scalarDerivative retained.val test point else 0 := by
      apply Finset.sum_congr rfl
      intro lower membership
      rw [scalarDerivative_mul order lower _ test
        (scalarDerivative_smooth _ scalar scalarSmooth) testSmooth]
      simp only [below, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro retained retainedMem
      by_cases bound : indexLE retained lower
      · rw [if_pos bound, if_pos bound,
          nested_difference_derivative upper lower retained ((mem_below _ _).mp membership)
            bound scalar scalarSmooth]
        ring
      · simp [bound]
    _ = ∑ retained : JetIndex order,
        (∑ lower ∈ below upper, if indexLE retained lower then
          (-1 : ℝ) ^ degree lower * binomial upper lower * binomial lower retained else 0) *
          scalarDerivative (difference upper retained).val scalar point *
          scalarDerivative retained.val test point := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro retained retainedMem
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro lower membership
      split_ifs <;> simp
    _ = _ := by
      simp_rw [binomial_cancellation]
      simp [difference, scalarDerivative_zero]

theorem scalar_consumer : ScalarLeibnizGoal :=
  ⟨scalarDerivative_comp, scalarDerivative_mul, binomial_cancellation, scalar_adjoint⟩

end Grad.WeightedJets.SpatialMultiplier
