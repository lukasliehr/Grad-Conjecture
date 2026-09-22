import WC3Interface

noncomputable section

open LineDeriv Grad.PDEBootstrap

namespace Grad.WeakPullback.Ordered

theorem directional_coordinates (direction : Spatial) (distribution : FieldDistribution) :
    lineDerivOp direction distribution =
      ∑ input : Fin 2, direction input • distributionDerivative input distribution := by
  calc
    _ = lineDerivOp (∑ input : Fin 2, direction input • spatialDirection input) distribution :=
      congrArg (fun vector : Spatial => lineDerivOp vector distribution)
        (OrthogonalCoefficients.Composition.spatialDirection_expansion direction)
    _ = ∑ input : Fin 2, lineDerivOp (direction input • spatialDirection input) distribution :=
      lineDerivOp_left_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro input _membership
      exact lineDerivOp_left_smul _ _ _

theorem rankOne : RankOneGoal := by
  intro output orthogonal distribution
  change lineDerivOp (spatialDirection output) (distributionPullback orthogonal distribution) = _
  rw [directional, directional_coordinates, map_sum]
  apply Finset.sum_congr rfl
  intro input _membership
  exact (distributionPullback orthogonal).toLinearMap.map_smul_of_tower _ _

theorem orderedDerivative_cons (rank : ℕ) (head : Fin 2) (tail : Fin rank → Fin 2)
    (distribution : FieldDistribution) :
    orderedDerivative (rank + 1) (Fin.cons head tail) distribution =
      distributionDerivative head (orderedDerivative rank tail distribution) := rfl

theorem sum_words_succ (rank : ℕ) (summand : (Fin (rank + 1) → Fin 2) → FieldDistribution) :
    ∑ input : Fin (rank + 1) → Fin 2, summand input =
      ∑ head : Fin 2, ∑ tail : Fin rank → Fin 2, summand (Fin.cons head tail) := by
  calc
    _ = ∑ pair : Fin 2 × (Fin rank → Fin 2), summand (Fin.cons pair.1 pair.2) :=
      ((Fin.consEquiv (fun _ : Fin (rank + 1) => Fin 2)).sum_comp summand).symm
    _ = _ := Fintype.sum_prod_type _

theorem distributionDerivative_real_smul (output : Fin 2) (scalar : ℝ)
    (distribution : FieldDistribution) :
    distributionDerivative output (scalar • distribution) =
      scalar • distributionDerivative output distribution :=
  (distributionDerivative output).toLinearMap.map_smul_of_tower scalar distribution

theorem chain : ChainGoal := by
  intro rank
  induction rank with
  | zero =>
      intro word orthogonal distribution
      simp [orderedDerivative_zero]
  | succ rank inductionHypothesis =>
      intro word orthogonal distribution
      rw [orderedDerivative_succ, inductionHypothesis]
      change distributionDerivative (word 0) _ = _
      rw [map_sum, sum_words_succ, ← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tail _tailMembership
      rw [distributionDerivative_real_smul, rankOne, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro head _headMembership
      rw [smul_smul, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_def, orderedDerivative_cons]
      rw [mul_comm]

end Grad.WeakPullback.Ordered
