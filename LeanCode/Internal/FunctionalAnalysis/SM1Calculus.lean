import SM1Interface

noncomputable section

open Grad.PDEBootstrap
open Grad.WeakTesting.Commutation (differentiate listDerivative)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem canonical_list (zeros ones : ℕ) :
    List.ofFn (Grad.WeakTesting.Commutation.canonicalWord zeros ones) =
      List.replicate zeros 0 ++ List.replicate ones 1 := by
  rw [List.ofFn_add]
  have first : (fun position : Fin zeros =>
      Grad.WeakTesting.Commutation.canonicalWord zeros ones (Fin.castLE (Nat.le_add_right zeros ones) position)) =
      fun _ => (0 : Fin 2) := by
    funext position
    simp [Grad.WeakTesting.Commutation.canonicalWord, position.isLt]
  have second : (fun position : Fin ones =>
      Grad.WeakTesting.Commutation.canonicalWord zeros ones (Fin.natAdd zeros position)) =
      fun _ => (1 : Fin 2) := by
    funext position
    simp [Grad.WeakTesting.Commutation.canonicalWord]
  rw [first, second, List.ofFn_const, List.ofFn_const]

theorem listDerivative_append (first second : List (Fin 2)) (scalar : Spatial → ℝ) :
    listDerivative (first ++ second) scalar =
      listDerivative first (listDerivative second scalar) := by
  simp only [listDerivative, List.foldr_append]

theorem scalarDerivative_list (index : ℕ × ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    scalarDerivative index scalar =
      listDerivative (List.replicate index.1 0 ++ List.replicate index.2 1) scalar := by
  rw [scalarDerivative, ← Grad.WeakTesting.Commutation.listDerivative_ofFn _ _ _ smoothness,
    canonical_list]

theorem scalarDerivative_comp (first second : ℕ × ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    scalarDerivative first (scalarDerivative second scalar) =
      scalarDerivative (first.1 + second.1, first.2 + second.2) scalar := by
  rw [scalarDerivative_list first _ (scalarDerivative_smooth second scalar smoothness),
    scalarDerivative_list second scalar smoothness,
    scalarDerivative_list _ scalar smoothness, ← listDerivative_append]
  apply Grad.WeakTesting.Commutation.listDerivative_perm _ scalar smoothness
  apply List.perm_iff_count.mpr
  intro direction
  simp only [List.count_append, List.count_replicate]
  split_ifs <;> omega

def repeatDerivative (direction : Fin 2) (rank : ℕ) (scalar : Spatial → ℝ) : Spatial → ℝ :=
  listDerivative (List.replicate rank direction) scalar

theorem repeatDerivative_smooth (direction : Fin 2) (rank : ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    ContDiff ℝ ∞ (repeatDerivative direction rank scalar) :=
  Grad.WeakTesting.Commutation.listDerivative_contDiff _ _ smoothness

theorem repeatDerivative_zero (direction : Fin 2) (scalar : Spatial → ℝ) :
    repeatDerivative direction 0 scalar = scalar := rfl

theorem repeatDerivative_succ (direction : Fin 2) (rank : ℕ) (scalar : Spatial → ℝ) :
    repeatDerivative direction (rank + 1) scalar =
      differentiate direction (repeatDerivative direction rank scalar) := by
  simp only [repeatDerivative, List.replicate_succ, listDerivative, List.foldr_cons]

theorem differentiate_mul (direction : Fin 2) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    differentiate direction (fun point => first point * second point) =
      fun point => differentiate direction first point * second point +
        first point * differentiate direction second point := by
  funext point
  rw [differentiate, fderiv_fun_mul (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change first point * differentiate direction second point +
    second point * differentiate direction first point = _
  ring

theorem differentiate_sum {Index : Type*} (indices : Finset Index) (direction : Fin 2)
    (family : Index → Spatial → ℝ) (smoothness : ∀ index ∈ indices, ContDiff ℝ ∞ (family index)) :
    differentiate direction (fun point => ∑ index ∈ indices, family index point) =
      fun point => ∑ index ∈ indices, differentiate direction (family index) point := by
  funext point
  rw [differentiate, fderiv_fun_sum (fun index membership =>
    (smoothness index membership).differentiable (by simp) point)]
  simp only [sum_apply, differentiate]

theorem differentiate_const_mul (direction : Fin 2) (constant : ℝ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    differentiate direction (fun point => constant * scalar point) =
      fun point => constant * differentiate direction scalar point := by
  rw [differentiate_mul direction (fun _ => constant) scalar contDiff_const smoothness]
  simp [differentiate]

theorem repeatDerivative_mul (direction : Fin 2) (rank : ℕ) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    repeatDerivative direction rank (fun point => first point * second point) =
      fun point => ∑ index ∈ Finset.range (rank + 1), (rank.choose index : ℝ) *
        (repeatDerivative direction index first point *
          repeatDerivative direction (rank - index) second point) := by
  induction rank with
  | zero => simp [repeatDerivative_zero]
  | succ rank induction =>
    rw [repeatDerivative_succ, induction,
      differentiate_sum _ direction _ (by
        intro index membership
        exact contDiff_const.mul ((repeatDerivative_smooth direction index first firstSmooth).mul
          (repeatDerivative_smooth direction (rank - index) second secondSmooth)))]
    funext point
    simp only [differentiate_const_mul direction _ _
      ((repeatDerivative_smooth direction _ first firstSmooth).mul
        (repeatDerivative_smooth direction _ second secondSmooth)),
      differentiate_mul direction _ _
        (repeatDerivative_smooth direction _ first firstSmooth)
        (repeatDerivative_smooth direction _ second secondSmooth),
      ← repeatDerivative_succ]
    rw [Finset.sum_choose_succ_mul (fun firstRank secondRank =>
      repeatDerivative direction firstRank first point *
        repeatDerivative direction secondRank second point) rank]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index membership
    have bound : index ≤ rank := Nat.le_of_lt_succ (Finset.mem_range.mp membership)
    have subtraction : rank + 1 - index = rank - index + 1 := by omega
    rw [subtraction]
    ring

end Grad.WeightedJets.SpatialMultiplier
