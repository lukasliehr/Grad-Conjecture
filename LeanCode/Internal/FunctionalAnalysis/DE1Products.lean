import DE1Finite

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem gaussian_positive (index : ℕ) : 0 < gaussian index := Real.rpow_pos_of_pos (by norm_num) _

theorem gaussian_succ (index : ℕ) : gaussian (index + 1) = gaussian index / node (index + 1) := by
  unfold gaussian node
  rw [← Real.rpow_sub_natCast (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

theorem sum_nodes (count : ℕ) : ∑ index ∈ Finset.range count, node index = node count - 1 := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis, node_succ]
      ring

theorem sum_inverse_nodes (count : ℕ) :
    ∑ index ∈ Finset.range count, (node index)⁻¹ = 2 - 2 / node count := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis, node_succ]
      field_simp
      ring

theorem sum_inverse_nodes_le_two (count : ℕ) :
    ∑ index ∈ Finset.range count, (node index)⁻¹ ≤ 2 := by
  rw [sum_inverse_nodes]
  exact sub_le_self _ (div_nonneg (by norm_num) (node_positive count).le)

theorem sum_shift_inverse_nodes (count : ℕ) :
    ∑ index ∈ Finset.range count, (node (index + 1))⁻¹ = 1 - (node count)⁻¹ := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis, node_succ]
      field_simp
      ring

theorem sum_shift_inverse_nodes_le_one (count : ℕ) :
    ∑ index ∈ Finset.range count, (node (index + 1))⁻¹ ≤ 1 := by
  rw [sum_shift_inverse_nodes]
  exact sub_le_self _ (inv_nonneg.mpr (node_positive count).le)

theorem ratio_half (first second : ℕ) (ordered : first < second) :
    node first / node second ≤ 1 / 2 := by
  have comparison := node_strictMono.monotone (show first + 1 ≤ second by omega)
  rw [node_succ] at comparison
  apply (div_le_iff₀ (node_positive second)).mpr
  linarith

def relative (index other : ℕ) : ℝ :=
  if other < index then node other / node index else node index / node other

def lowerScale (index other : ℕ) : ℝ :=
  if other < index then node other / node index else 1

theorem relative_nonnegative (index other : ℕ) : 0 ≤ relative index other := by
  unfold relative
  split_ifs
  · exact div_nonneg (node_positive other).le (node_positive index).le
  · exact div_nonneg (node_positive index).le (node_positive other).le

theorem lowerScale_nonnegative (index other : ℕ) : 0 ≤ lowerScale index other := by
  unfold lowerScale
  split_ifs
  · exact div_nonneg (node_positive other).le (node_positive index).le
  · norm_num

theorem relative_half (index other : ℕ) (distinct : other ≠ index) : relative index other ≤ 1 / 2 := by
  unfold relative
  split_ifs with ordered
  · exact ratio_half other index ordered
  · exact ratio_half index other (by omega)

theorem relative_self (index : ℕ) : relative index index = 1 := by
  simp [relative, (node_positive index).ne']

theorem relative_prefix (index : ℕ) : ∑ other ∈ Finset.range (index + 1), relative index other ≤ 2 := by
  rw [Finset.sum_range_succ, relative_self]
  have equality : (∑ other ∈ Finset.range index, relative index other) =
      (node index - 1) / node index := by
    calc
      _ = ∑ other ∈ Finset.range index, node other / node index :=
        Finset.sum_congr rfl (fun other membership => if_pos (Finset.mem_range.mp membership))
      _ = _ := by simp only [div_eq_mul_inv, ← Finset.sum_mul, sum_nodes]
  rw [equality]
  have bound : (node index - 1) / node index ≤ 1 :=
    (div_le_one (node_positive index)).mpr (by linarith)
  linarith

theorem relative_shift (index offset : ℕ) : relative index (index + 1 + offset) = (node (offset + 1))⁻¹ := by
  rw [relative, if_neg (by omega : ¬index + 1 + offset < index)]
  rw [show index + 1 + offset = index + (offset + 1) by omega, node_add]
  field_simp [(node_positive index).ne', (node_positive (offset + 1)).ne']

theorem relative_sum (cutoff index : ℕ) (retained : index ≤ cutoff) :
    ∑ other ∈ (Finset.range (cutoff + 1)).erase index, relative index other ≤ 2 := by
  have total : ∑ other ∈ Finset.range (cutoff + 1), relative index other ≤ 3 := by
    rw [show cutoff + 1 = (index + 1) + (cutoff - index) by omega, Finset.sum_range_add]
    have shifted : (∑ offset ∈ Finset.range (cutoff - index), relative index (index + 1 + offset)) ≤ 1 := by
      simp_rw [relative_shift]
      exact sum_shift_inverse_nodes_le_one _
    linarith [relative_prefix index]
  have erase := Finset.sum_erase_add (Finset.range (cutoff + 1)) (relative index)
    (show index ∈ Finset.range (cutoff + 1) by simpa using retained)
  rw [relative_self] at erase
  linarith

theorem lower_product (index : ℕ) :
    ∏ other ∈ Finset.range index, node other / node index = gaussian index := by
  induction index with
  | zero => norm_num [gaussian]
  | succ index inductionHypothesis =>
      rw [Finset.prod_range_succ]
      have ratio (other : ℕ) : node other / node (index + 1) = (node other / node index) / 2 := by
        rw [node_succ, div_mul_eq_div_div]
      simp_rw [ratio]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, inductionHypothesis,
        div_self (node_positive index).ne', gaussian_succ, node_succ]
      unfold node
      ring

theorem lowerScale_product (cutoff index : ℕ) (retained : index ≤ cutoff) :
    ∏ other ∈ (Finset.range (cutoff + 1)).erase index, lowerScale index other = gaussian index := by
  have subset : Finset.range index ⊆ (Finset.range (cutoff + 1)).erase index := by
    intro other membership
    simp only [Finset.mem_erase, Finset.mem_range] at *
    omega
  have equality := Finset.prod_subset (f := lowerScale index) subset (by
    intro other _membership outside
    exact if_neg (by simpa using outside))
  rw [← equality]
  calc
    _ = ∏ other ∈ Finset.range index, node other / node index :=
      Finset.prod_congr rfl (fun other membership => if_pos (Finset.mem_range.mp membership))
    _ = _ := lower_product index

end Grad.DiskExtension.Seeley
