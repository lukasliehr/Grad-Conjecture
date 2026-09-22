import AQ3Allocation

noncomputable section

open scoped BigOperators

namespace Grad.TameAllocation

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

omit [DecidableEq Index] in
theorem allocated_weights (orders : Index → ℕ) (total : ℕ) (positive : 0 < total)
    (allocated : ∑ index, orders index ≤ total) :
    (∀ index, 0 ≤ (orders index : ℝ) / total) ∧ ∑ index, (orders index : ℝ) / total ≤ 1 := by
  have realPositive : 0 < (total : ℝ) := by exact_mod_cast positive
  constructor
  · intro index
    positivity
  · rw [← Finset.sum_div]
    apply (div_le_one realPositive).mpr
    exact_mod_cast allocated

theorem natural_allocation (low high : Index → ℝ) (orders : Index → ℕ) (total : ℕ)
    (positive : 0 < total) (allocated : ∑ index, orders index ≤ total)
    (lowNonnegative : ∀ index, 0 ≤ low index) (highNonnegative : ∀ index, 0 ≤ high index) :
    ∏ index, low index ^ (1 - (orders index : ℝ) / total) * high index ^ ((orders index : ℝ) / total) ≤
      (∏ index, low index) + ∑ index, high index * ∏ other ∈ Finset.univ.erase index, low other := by
  have weights := allocated_weights orders total positive allocated
  exact one_high_sum low high (fun index => (orders index : ℝ) / total)
    lowNonnegative highNonnegative weights.1 weights.2

theorem exact_natural_allocation (low high : Index → ℝ) (orders : Index → ℕ) (total : ℕ)
    (positive : 0 < total) (allocated : ∑ index, orders index = total)
    (lowNonnegative : ∀ index, 0 ≤ low index) (highNonnegative : ∀ index, 0 ≤ high index) :
    ∏ index, low index ^ (1 - (orders index : ℝ) / total) * high index ^ ((orders index : ℝ) / total) ≤
      ∑ index, high index * ∏ other ∈ Finset.univ.erase index, low other := by
  have weights := allocated_weights orders total positive allocated.le
  apply one_high_sum_exact low high (fun index => (orders index : ℝ) / total)
    lowNonnegative highNonnegative weights.1
  rw [← Finset.sum_div]
  have realSum : ∑ index, (orders index : ℝ) = total := by exact_mod_cast allocated
  rw [realSum, div_self (by exact_mod_cast positive.ne')]

omit [DecidableEq Index] in
theorem common_natural_allocation [Nonempty Index] (low high : ℝ) (orders : Index → ℕ) (total : ℕ)
    (positive : 0 < total) (allocated : ∑ index, orders index ≤ total)
    (lowNonnegative : 0 ≤ low) (lowHigh : low ≤ high) :
    ∏ index, low ^ (1 - (orders index : ℝ) / total) * high ^ ((orders index : ℝ) / total) ≤
      low ^ (Fintype.card Index - 1) * high := by
  classical
  have weights := allocated_weights orders total positive allocated
  exact common_one_high low high (fun index => (orders index : ℝ) / total)
    lowNonnegative lowHigh weights.1 weights.2

omit [DecidableEq Index] in
theorem interpolated_product_bound [Nonempty Index] (factors constants : Index → ℝ)
    (low high : ℝ) (orders : Index → ℕ) (total : ℕ)
    (positive : 0 < total) (allocated : ∑ index, orders index ≤ total)
    (lowNonnegative : 0 ≤ low) (lowHigh : low ≤ high)
    (factorsNonnegative : ∀ index, 0 ≤ factors index)
    (constantsNonnegative : ∀ index, 0 ≤ constants index)
    (interpolated : ∀ index, factors index ≤ constants index *
      (low ^ (1 - (orders index : ℝ) / total) * high ^ ((orders index : ℝ) / total))) :
    ∏ index, factors index ≤ (∏ index, constants index) * low ^ (Fintype.card Index - 1) * high := by
  calc
    _ ≤ ∏ index, constants index *
        (low ^ (1 - (orders index : ℝ) / total) * high ^ ((orders index : ℝ) / total)) :=
      Finset.prod_le_prod (fun index _ => factorsNonnegative index) (fun index _ => interpolated index)
    _ = (∏ index, constants index) *
        ∏ index, low ^ (1 - (orders index : ℝ) / total) * high ^ ((orders index : ℝ) / total) :=
      Finset.prod_mul_distrib
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (common_natural_allocation low high orders total positive allocated lowNonnegative lowHigh)
        (Finset.prod_nonneg (fun index _ => constantsNonnegative index))

end Grad.TameAllocation
