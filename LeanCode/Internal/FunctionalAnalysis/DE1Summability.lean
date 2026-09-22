import DE1Limit

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem momentMajorant_nonnegative (order index : ℕ) : 0 ≤ momentMajorant order index :=
  mul_nonneg (coefficientBound_positive index).le (pow_nonneg (node_positive index).le order)

theorem momentMajorant_succ (order index : ℕ) :
    momentMajorant order (index + 1) =
      momentMajorant order index * (node order / node (index + 1)) := by
  have nodePower : node (index + 1) ^ order = node index ^ order * node order := by
    rw [node_succ, mul_pow]
    rfl
  unfold momentMajorant coefficientBound
  rw [gaussian_succ, nodePower]
  field_simp [(node_positive (index + 1)).ne']

theorem momentMajorant_ratio (order index : ℕ) (large : order ≤ index) :
    momentMajorant order (index + 1) ≤ (1 / 2 : ℝ) * momentMajorant order index := by
  rw [momentMajorant_succ]
  calc
    _ ≤ momentMajorant order index * (1 / 2) :=
      mul_le_mul_of_nonneg_left (ratio_half order (index + 1) (by omega))
        (momentMajorant_nonnegative order index)
    _ = _ := by ring

theorem momentMajorant_summable (order : ℕ) : Summable (momentMajorant order) := by
  apply summable_of_ratio_norm_eventually_le (show (1 / 2 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop order] with index large
  simpa only [Real.norm_eq_abs, abs_of_nonneg (momentMajorant_nonnegative order (index + 1)),
    abs_of_nonneg (momentMajorant_nonnegative order index)] using
      momentMajorant_ratio order index large

theorem coefficient_moment_bound (order index : ℕ) :
    |coefficient index| * node index ^ order ≤ momentMajorant order index := by
  exact mul_le_mul_of_nonneg_right (coefficient_bound index)
    (pow_nonneg (node_positive index).le order)

theorem coefficient_absolute_moment_summable (order : ℕ) :
    Summable (fun index => |coefficient index| * node index ^ order) := by
  exact (momentMajorant_summable order).of_nonneg_of_le
    (fun index => mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le order))
    (coefficient_moment_bound order)

theorem coefficient_signed_moment_summable (order : ℕ) :
    Summable (fun index => coefficient index * (-node index) ^ order) := by
  apply (momentMajorant_summable order).of_norm_bounded
  intro index
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (node_positive index)] using
    coefficient_moment_bound order index

theorem absoluteMoment_nonnegative (order : ℕ) : 0 ≤ absoluteMoment order := by
  exact tsum_nonneg (fun index => mul_nonneg (abs_nonneg _)
    (pow_nonneg (node_positive index).le order))

theorem absoluteMoment_bound (order : ℕ) :
    absoluteMoment order ≤ ∑' index, momentMajorant order index := by
  exact Summable.tsum_le_tsum (coefficient_moment_bound order)
    (coefficient_absolute_moment_summable order) (momentMajorant_summable order)

theorem coefficient_absolute_tail (order : ℕ) :
    Tendsto (fun cutoff => ∑' index,
      |coefficient (cutoff + index)| * node (cutoff + index) ^ order) atTop (nhds 0) := by
  simpa only [Nat.add_comm] using
    tendsto_sum_nat_add (fun index => |coefficient index| * node index ^ order)

theorem summability_goal : SummabilityGoal :=
  ⟨momentMajorant_summable, coefficient_absolute_moment_summable,
    coefficient_signed_moment_summable,
    fun order => ⟨absoluteMoment_nonnegative order, absoluteMoment_bound order⟩,
    coefficient_absolute_tail⟩

end Grad.DiskExtension.Seeley
