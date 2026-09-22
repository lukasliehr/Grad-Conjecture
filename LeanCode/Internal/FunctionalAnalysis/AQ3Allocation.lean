import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

open scoped BigOperators Topology

namespace Grad.TameAllocation

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

omit [DecidableEq Index] in
theorem weighted_geometric_bound (weights values : Index → ℝ)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index ≤ 1)
    (valuesNonnegative : ∀ index, 0 ≤ values index) :
    ∏ index, values index ^ weights index ≤
      1 - ∑ index, weights index + ∑ index, weights index * values index := by
  classical
  let extendedWeight : Option Index → ℝ := fun index =>
    index.elim (1 - ∑ position, weights position) weights
  let extendedValue : Option Index → ℝ := fun index => index.elim 1 values
  have nonnegative : ∀ index, 0 ≤ extendedWeight index := by
    intro index
    cases index with
    | none => exact sub_nonneg.mpr weightSum
    | some index => exact weightsNonnegative index
  have total : ∑ index, extendedWeight index = 1 := by
    simp [Fintype.sum_option, extendedWeight]
  have valuesBound : ∀ index, 0 ≤ extendedValue index := by
    intro index
    cases index with
    | none => exact zero_le_one
    | some index => exact valuesNonnegative index
  have inequality := Real.geom_mean_le_arith_mean_weighted Finset.univ extendedWeight extendedValue
    (fun index _ => nonnegative index) total (fun index _ => valuesBound index)
  simpa [Fintype.prod_option, Fintype.sum_option, extendedWeight, extendedValue] using inequality

theorem positive_interpolation_factor (low high exponent : ℝ)
    (lowPositive : 0 < low) (highNonnegative : 0 ≤ high) :
    low ^ (1 - exponent) * high ^ exponent = low * (high / low) ^ exponent := by
  rw [Real.rpow_sub lowPositive, Real.rpow_one, Real.div_rpow highNonnegative lowPositive.le]
  ring

theorem positive_weighted_one_high (low high weights : Index → ℝ)
    (lowPositive : ∀ index, 0 < low index)
    (highNonnegative : ∀ index, 0 ≤ high index)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index ≤ 1) :
    ∏ index, low index ^ (1 - weights index) * high index ^ weights index ≤
      (1 - ∑ index, weights index) * ∏ index, low index +
        ∑ index, weights index * high index * ∏ other ∈ Finset.univ.erase index, low other := by
  classical
  have inequality := mul_le_mul_of_nonneg_left
    (weighted_geometric_bound weights (fun index => high index / low index)
      weightsNonnegative weightSum (fun index => div_nonneg (highNonnegative index) (lowPositive index).le))
    (show 0 ≤ ∏ index, low index from Finset.prod_nonneg (fun index _ => (lowPositive index).le))
  calc
    _ = (∏ index, low index) * ∏ index, (high index / low index) ^ weights index := by
      simp_rw [positive_interpolation_factor _ _ _ (lowPositive _) (highNonnegative _)]
      exact Finset.prod_mul_distrib
    _ ≤ (∏ index, low index) *
        (1 - ∑ index, weights index + ∑ index, weights index * (high index / low index)) := inequality
    _ = _ := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro index _
        rw [← Finset.mul_prod_erase Finset.univ low (Finset.mem_univ index)]
        field_simp [(lowPositive index).ne']

omit [DecidableEq Index] in
theorem weight_le_one (weights : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ weights index)
    (total : ∑ index, weights index ≤ 1) (index : Index) : weights index ≤ 1 :=
  (Finset.single_le_sum (fun position _ => nonnegative position) (Finset.mem_univ index)).trans total

theorem weighted_one_high (low high weights : Index → ℝ)
    (lowNonnegative : ∀ index, 0 ≤ low index)
    (highNonnegative : ∀ index, 0 ≤ high index)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index ≤ 1) :
    ∏ index, low index ^ (1 - weights index) * high index ^ weights index ≤
      (1 - ∑ index, weights index) * ∏ index, low index +
        ∑ index, weights index * high index * ∏ other ∈ Finset.univ.erase index, low other := by
  have leftContinuous : Continuous (fun epsilon : ℝ =>
      ∏ index, (low index + epsilon) ^ (1 - weights index) * (high index + epsilon) ^ weights index) := by
    apply continuous_finsetProd
    intro index _
    exact ((Real.continuous_rpow_const
      (sub_nonneg.mpr (weight_le_one weights weightsNonnegative weightSum index))).comp
      (continuous_const.add continuous_id)).mul
      ((Real.continuous_rpow_const (weightsNonnegative index)).comp (continuous_const.add continuous_id))
  have rightContinuous : Continuous (fun epsilon : ℝ =>
      (1 - ∑ index, weights index) * ∏ index, (low index + epsilon) +
        ∑ index, weights index * (high index + epsilon) *
          ∏ other ∈ Finset.univ.erase index, (low other + epsilon)) := by
    fun_prop
  have inequality := le_of_tendsto_of_tendsto
    (leftContinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (rightContinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (show ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      (∏ index, (low index + epsilon) ^ (1 - weights index) * (high index + epsilon) ^ weights index) ≤
        (1 - ∑ index, weights index) * ∏ index, (low index + epsilon) +
          ∑ index, weights index * (high index + epsilon) *
            ∏ other ∈ Finset.univ.erase index, (low other + epsilon) from by
      filter_upwards [self_mem_nhdsWithin] with epsilon positive
      exact positive_weighted_one_high (fun index => low index + epsilon)
        (fun index => high index + epsilon) weights
        (fun index => add_pos_of_nonneg_of_pos (lowNonnegative index) positive)
        (fun index => add_nonneg (highNonnegative index) positive.le) weightsNonnegative weightSum)
  simpa only [add_zero] using inequality

theorem one_high_sum (low high weights : Index → ℝ)
    (lowNonnegative : ∀ index, 0 ≤ low index)
    (highNonnegative : ∀ index, 0 ≤ high index)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index ≤ 1) :
    ∏ index, low index ^ (1 - weights index) * high index ^ weights index ≤
      (∏ index, low index) + ∑ index, high index * ∏ other ∈ Finset.univ.erase index, low other := by
  refine (weighted_one_high low high weights lowNonnegative highNonnegative weightsNonnegative weightSum).trans ?_
  apply add_le_add
  · have sumNonnegative : 0 ≤ ∑ index, weights index := Finset.sum_nonneg (fun index _ => weightsNonnegative index)
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun index _ => lowNonnegative index)) (by linarith)
  · apply Finset.sum_le_sum
    intro index _
    rw [mul_assoc]
    exact mul_le_of_le_one_left
      (mul_nonneg (highNonnegative index) (Finset.prod_nonneg (fun other _ => lowNonnegative other)))
      (weight_le_one weights weightsNonnegative weightSum index)

theorem one_high_sum_exact (low high weights : Index → ℝ)
    (lowNonnegative : ∀ index, 0 ≤ low index)
    (highNonnegative : ∀ index, 0 ≤ high index)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index = 1) :
    ∏ index, low index ^ (1 - weights index) * high index ^ weights index ≤
      ∑ index, high index * ∏ other ∈ Finset.univ.erase index, low other := by
  have inequality := weighted_one_high low high weights lowNonnegative highNonnegative weightsNonnegative weightSum.le
  rw [weightSum, sub_self, zero_mul, zero_add] at inequality
  refine inequality.trans (Finset.sum_le_sum (fun index _ => ?_))
  rw [mul_assoc]
  exact mul_le_of_le_one_left
    (mul_nonneg (highNonnegative index) (Finset.prod_nonneg (fun other _ => lowNonnegative other)))
    (weight_le_one weights weightsNonnegative weightSum.le index)

theorem common_one_high [Nonempty Index] (low high : ℝ) (weights : Index → ℝ)
    (lowNonnegative : 0 ≤ low) (lowHigh : low ≤ high)
    (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (weightSum : ∑ index, weights index ≤ 1) :
    ∏ index, low ^ (1 - weights index) * high ^ weights index ≤
      low ^ (Fintype.card Index - 1) * high := by
  have inequality := weighted_one_high (fun _ => low) (fun _ => high) weights
    (fun _ => lowNonnegative) (fun _ => lowNonnegative.trans lowHigh) weightsNonnegative weightSum
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at inequality
  have cardPositive : 0 < Fintype.card Index := Fintype.card_pos
  have lowBound : low ^ Fintype.card Index ≤ low ^ (Fintype.card Index - 1) * high := by
    calc
      _ = low ^ (Fintype.card Index - 1) * low := by
        rw [← pow_succ, Nat.sub_add_cancel cardPositive]
      _ ≤ _ := mul_le_mul_of_nonneg_left lowHigh (pow_nonneg lowNonnegative _)
  refine inequality.trans ?_
  calc
    _ ≤ (1 - ∑ index, weights index) * (low ^ (Fintype.card Index - 1) * high) +
        ∑ index, weights index * high * low ^ (Fintype.card Index - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left lowBound (sub_nonneg.mpr weightSum)) le_rfl
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

end Grad.TameAllocation
