import DE1Products

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem inverse_one_sub_bound (value : ℝ) (nonnegative : 0 ≤ value) (small : value ≤ 1 / 2) :
    (1 - value)⁻¹ ≤ 1 + 2 * value := by
  rw [← one_div (1 - value)]
  apply (div_le_iff₀ (by linarith : 0 < 1 - value)).mpr
  nlinarith [mul_nonneg nonnegative (show 0 ≤ 1 - 2 * value by linarith)]

theorem factor_absolute (index other : ℕ) (distinct : other ≠ index) :
    |(1 + node other) / (node other - node index)| =
      lowerScale index other * (1 + (node other)⁻¹) * (1 - relative index other)⁻¹ := by
  have numerator : 0 < 1 + node other := by linarith [node_positive other]
  by_cases lower : other < index
  · have gap := sub_neg.mpr (node_strictMono lower)
    have positiveGap : 0 < node index - node other := sub_pos.mpr (node_strictMono lower)
    have scaleIdentity :
        node other / node index * (1 + (node other)⁻¹) = (1 + node other) / node index := by
      field_simp [(node_positive index).ne', (node_positive other).ne']
      ring
    have relativeIdentity :
        (1 - node other / node index)⁻¹ = node index / (node index - node other) := by
      field_simp [(node_positive index).ne', positiveGap.ne']
    simp only [relative, lowerScale, if_pos lower, abs_div, abs_of_pos numerator, abs_of_neg gap]
    rw [scaleIdentity, relativeIdentity]
    rw [show -(node other - node index) = node index - node other by ring]
    field_simp [(node_positive index).ne', positiveGap.ne']
  · have gap := sub_pos.mpr (node_strictMono (show index < other by omega))
    simp only [relative, lowerScale, if_neg lower, abs_div, abs_of_pos numerator, abs_of_pos gap, one_mul]
    field_simp [(node_positive index).ne', (node_positive other).ne', node_sub_ne_zero other index distinct]
    ring

theorem factor_bound (index other : ℕ) (distinct : other ≠ index) :
    |(1 + node other) / (node other - node index)| ≤
      lowerScale index other * (1 + (node other)⁻¹) * (1 + 2 * relative index other) := by
  rw [factor_absolute index other distinct]
  exact mul_le_mul_of_nonneg_left
    (inverse_one_sub_bound _ (relative_nonnegative index other) (relative_half index other distinct))
    (mul_nonneg (lowerScale_nonnegative index other)
      (add_nonneg zero_le_one (inv_nonneg.mpr (node_positive other).le)))

theorem numerator_product_bound (cutoff index : ℕ) :
    ∏ other ∈ (Finset.range (cutoff + 1)).erase index, (1 + (node other)⁻¹) ≤ Real.exp 2 := by
  have bound : (∑ other ∈ (Finset.range (cutoff + 1)).erase index, (node other)⁻¹) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun other _membership _outside => inv_nonneg.mpr (node_positive other).le)).trans
        (sum_inverse_nodes_le_two (cutoff + 1))
  exact (Real.prod_one_add_le_exp_sum _ (fun other => inv_nonneg.mpr (node_positive other).le)).trans
    (Real.exp_le_exp.mpr bound)

theorem relative_product_bound (cutoff index : ℕ) (retained : index ≤ cutoff) :
    ∏ other ∈ (Finset.range (cutoff + 1)).erase index, (1 + 2 * relative index other) ≤ Real.exp 4 := by
  have bound : (∑ other ∈ (Finset.range (cutoff + 1)).erase index, 2 * relative index other) ≤ 4 := by
    rw [← Finset.mul_sum]
    linarith [relative_sum cutoff index retained]
  exact (Real.prod_one_add_le_exp_sum _ (fun other => mul_nonneg (by norm_num)
    (relative_nonnegative index other))).trans (Real.exp_le_exp.mpr bound)

theorem coefficientBound_positive (index : ℕ) : 0 < coefficientBound index :=
  mul_pos (Real.exp_pos 6) (gaussian_positive index)

theorem finite_bound (cutoff index : ℕ) : |finiteCoefficient cutoff index| ≤ coefficientBound index := by
  by_cases retained : index ≤ cutoff
  · rw [finiteCoefficient, if_pos retained, Finset.abs_prod]
    calc
      _ ≤ ∏ other ∈ (Finset.range (cutoff + 1)).erase index,
          lowerScale index other * (1 + (node other)⁻¹) * (1 + 2 * relative index other) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro other membership
        exact factor_bound index other (Finset.mem_erase.mp membership).1
      _ = (∏ other ∈ (Finset.range (cutoff + 1)).erase index, lowerScale index other) *
          (∏ other ∈ (Finset.range (cutoff + 1)).erase index, (1 + (node other)⁻¹)) *
          (∏ other ∈ (Finset.range (cutoff + 1)).erase index, (1 + 2 * relative index other)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ ≤ gaussian index * Real.exp 2 * Real.exp 4 := by
        rw [lowerScale_product cutoff index retained]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (numerator_product_bound cutoff index) (gaussian_positive index).le)
          (relative_product_bound cutoff index retained)
          (Finset.prod_nonneg (fun other _ => by linarith [relative_nonnegative index other]))
          (mul_nonneg (gaussian_positive index).le (Real.exp_pos 2).le)
      _ = coefficientBound index := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num [coefficientBound, mul_comm]
  · rw [finiteCoefficient, if_neg retained, abs_zero]
    exact (coefficientBound_positive index).le

theorem finite_moment_bound (cutoff order index : ℕ) :
    |finiteCoefficient cutoff index * (-node index) ^ order| ≤ momentMajorant order index := by
  rw [abs_mul, abs_pow, abs_neg, abs_of_pos (node_positive index)]
  exact mul_le_mul_of_nonneg_right (finite_bound cutoff index) (pow_nonneg (node_positive index).le order)

theorem uniform_goal : UniformGoal := ⟨finite_bound, finite_moment_bound⟩

end Grad.DiskExtension.Seeley
