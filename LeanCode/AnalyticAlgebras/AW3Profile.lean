import AW3Quadratic

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff BigOperators

namespace Grad.AnalyticWeights.Higher

theorem partition_size_sum {rank : ℕ} (partition : OrderedFinpartition rank) :
    ∑ block, partition.partSize block = rank := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr partition.equivSigma

def profileConstant (rank : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition rank, |sqrtCoefficient partition.length| * 2 ^ partition.length

theorem profileConstant_nonnegative (rank : ℕ) : 0 ≤ profileConstant rank := by
  unfold profileConstant
  positivity

theorem rational_power_cancel (coefficient root quadratic : ℝ) (rank blocks : ℕ)
    (positiveRank : 1 ≤ rank) (rootNonzero : root ≠ 0) (quadraticNonzero : quadratic ≠ 0) :
    (coefficient * root / quadratic ^ blocks) * ((2 * quadratic) ^ blocks / root ^ rank) =
      coefficient * 2 ^ blocks / root ^ (rank - 1) := by
  have powerSplit : root ^ rank = root ^ (rank - 1) * root := by
    rw [← pow_succ, Nat.sub_add_cancel positiveRank]
  rw [powerSplit, mul_pow]
  field_simp

theorem profile_partition_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial)
    (partition : OrderedFinpartition rank) :
    ‖partition.compAlongOrderedFinpartition
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (sqrtCoefficient partition.length * Real.sqrt (profileQuadratic point) /
            profileQuadratic point ^ partition.length))
        (fun block => iteratedFDeriv ℝ (partition.partSize block) profileQuadratic point)‖ ≤
      (|sqrtCoefficient partition.length| * 2 ^ partition.length) /
        Real.sqrt (profileQuadratic point) ^ (rank - 1) := by
  have quadraticPositive := profileQuadratic_pos point
  have rootPositive := Real.sqrt_pos.mpr quadraticPositive
  calc
    _ ≤ ‖ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (sqrtCoefficient partition.length * Real.sqrt (profileQuadratic point) /
            profileQuadratic point ^ partition.length)‖ *
        ∏ block, ‖iteratedFDeriv ℝ (partition.partSize block) profileQuadratic point‖ :=
      partition.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ (|sqrtCoefficient partition.length| * Real.sqrt (profileQuadratic point) /
          profileQuadratic point ^ partition.length) *
        ∏ block, (2 * profileQuadratic point /
          Real.sqrt (profileQuadratic point) ^ partition.partSize block) := by
      rw [LinearIsometryEquiv.norm_map, norm_div, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg rootPositive.le, norm_pow, Real.norm_of_nonneg quadraticPositive.le]
      apply mul_le_mul_of_nonneg_left
      · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun block _ =>
          profileQuadratic_iterated_norm_bound _ (partition.partSize_pos block) point)
      · positivity
    _ = _ := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, partition_size_sum]
      exact rational_power_cancel _ _ _ rank partition.length positiveRank rootPositive.ne' quadraticPositive.ne'

theorem profile_iterated_norm_decay (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank profile point‖ ≤
      profileConstant rank / Real.sqrt (1 + ‖point‖ ^ 2) ^ (rank - 1) := by
  rw [profile_rational_expansion rank positiveRank point]
  calc
    _ ≤ ∑ partition : OrderedFinpartition rank, _ := norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition rank,
        (|sqrtCoefficient partition.length| * 2 ^ partition.length) /
          Real.sqrt (profileQuadratic point) ^ (rank - 1) :=
      Finset.sum_le_sum (fun partition _ => profile_partition_bound rank positiveRank point partition)
    _ = _ := by rw [← Finset.sum_div]; rfl

theorem profile_radial_iterated_norm_decay (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖point‖ * ‖iteratedFDeriv ℝ (rank + 1) profile point‖ ≤
      profileConstant (rank + 1) / Real.sqrt (1 + ‖point‖ ^ 2) ^ (rank - 1) := by
  have rootPositive : 0 < Real.sqrt (1 + ‖point‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have normBound : ‖point‖ ≤ Real.sqrt (1 + ‖point‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have powerSplit : Real.sqrt (1 + ‖point‖ ^ 2) ^ rank =
      Real.sqrt (1 + ‖point‖ ^ 2) ^ (rank - 1) * Real.sqrt (1 + ‖point‖ ^ 2) := by
    rw [← pow_succ, Nat.sub_add_cancel positiveRank]
  calc
    _ ≤ ‖point‖ * (profileConstant (rank + 1) / Real.sqrt (1 + ‖point‖ ^ 2) ^ rank) :=
      mul_le_mul_of_nonneg_left (by simpa using profile_iterated_norm_decay (rank + 1) (by omega) point)
        (norm_nonneg _)
    _ ≤ Real.sqrt (1 + ‖point‖ ^ 2) *
        (profileConstant (rank + 1) / Real.sqrt (1 + ‖point‖ ^ 2) ^ rank) :=
      mul_le_mul_of_nonneg_right normBound (div_nonneg (profileConstant_nonnegative _) (by positivity))
    _ = _ := by rw [powerSplit]; field_simp

end Grad.AnalyticWeights.Higher
