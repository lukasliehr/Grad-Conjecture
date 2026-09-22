import CM1Weights
import CK2Data

noncomputable section

open scoped BigOperators

namespace Grad.RepresentedKernel.Composition.Moments

theorem finite_weighted_summability {Index : Type*} (indices : Finset Index)
    (weight bound : Index → ℝ) (entry : Index → ℤ → ℝ)
    (weightNonnegative : ∀ index ∈ indices, 0 ≤ weight index)
    (entrySummable : ∀ index ∈ indices, Summable (entry index))
    (entryBound : ∀ index ∈ indices, ∑' cell : ℤ, entry index cell ≤ bound index) :
    Summable (fun cell : ℤ => ∑ index ∈ indices, weight index * entry index cell) ∧
      (∑' cell : ℤ, ∑ index ∈ indices, weight index * entry index cell) ≤
        ∑ index ∈ indices, weight index * bound index := by
  have weighted (index : Index) (membership : index ∈ indices) :
      Summable (fun cell : ℤ => weight index * entry index cell) :=
    (entrySummable index membership).mul_left (weight index)
  refine ⟨(hasSum_sum (fun index membership => (weighted index membership).hasSum)).summable, ?_⟩
  rw [Summable.tsum_finsetSum weighted]
  apply Finset.sum_le_sum
  intro index membership
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (entryBound index membership) (weightNonnegative index membership)

def allocatedWeight (moment : ℕ) (outer inner : ℕ → ℤ → ℤ → ℝ) (output input : ℤ) : ℝ :=
  ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℝ) *
    ∑' middle : ℤ, outer allocation output middle * inner (moment - allocation) middle input

def allocatedBound (moment : ℕ) (outer inner : ℕ → ℝ) : ℝ :=
  ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℝ) *
    (outer allocation * inner (moment - allocation))

theorem allocatedWeight_nonnegative (moment : ℕ) (outer inner : ℕ → ℤ → ℤ → ℝ)
    (outerNonnegative : ∀ allocation output input, 0 ≤ outer allocation output input)
    (innerNonnegative : ∀ allocation output input, 0 ≤ inner allocation output input)
    (output input : ℤ) : 0 ≤ allocatedWeight moment outer inner output input :=
  Finset.sum_nonneg (fun allocation _membership => mul_nonneg (Nat.cast_nonneg _)
    (tsum_nonneg (fun middle => mul_nonneg (outerNonnegative allocation output middle)
      (innerNonnegative (moment - allocation) middle input))))

theorem allocated_rows (moment : ℕ) (outer inner : ℕ → ℤ → ℤ → ℝ)
    (outerBound innerBound : ℕ → ℝ)
    (outerNonnegative : ∀ allocation output input, 0 ≤ outer allocation output input)
    (innerNonnegative : ∀ allocation output input, 0 ≤ inner allocation output input)
    (outerRows : ∀ allocation output, Summable (outer allocation output))
    (innerRows : ∀ allocation output, Summable (inner allocation output))
    (outerBounded : ∀ allocation output, ∑' input, outer allocation output input ≤ outerBound allocation)
    (innerBounded : ∀ allocation output, ∑' input, inner allocation output input ≤ innerBound allocation)
    (innerBoundNonnegative : ∀ allocation, 0 ≤ innerBound allocation) (output : ℤ) :
    Summable (allocatedWeight moment outer inner output) ∧
      (∑' input : ℤ, allocatedWeight moment outer inner output input) ≤ allocatedBound moment outerBound innerBound := by
  have each (allocation : ℕ) := Countable.row_product_summable
    (outer allocation) (inner (moment - allocation)) (outerBound allocation) (innerBound (moment - allocation))
    (outerNonnegative allocation) (innerNonnegative (moment - allocation))
    (outerRows allocation) (innerRows (moment - allocation))
    (outerBounded allocation) (innerBounded (moment - allocation))
    (innerBoundNonnegative (moment - allocation)) output
  exact finite_weighted_summability (Finset.range (moment + 1)) (fun allocation => (moment.choose allocation : ℝ))
    (fun allocation => outerBound allocation * innerBound (moment - allocation))
    (fun allocation input => ∑' middle : ℤ, outer allocation output middle * inner (moment - allocation) middle input)
    (fun _ _ => Nat.cast_nonneg _) (fun allocation _ => (each allocation).2.1)
    (fun allocation _ => (each allocation).2.2)

theorem allocated_columns (moment : ℕ) (outer inner : ℕ → ℤ → ℤ → ℝ)
    (outerBound innerBound : ℕ → ℝ)
    (outerNonnegative : ∀ allocation output input, 0 ≤ outer allocation output input)
    (innerNonnegative : ∀ allocation output input, 0 ≤ inner allocation output input)
    (outerColumns : ∀ allocation input, Summable (fun output => outer allocation output input))
    (innerColumns : ∀ allocation input, Summable (fun output => inner allocation output input))
    (outerBounded : ∀ allocation input, ∑' output, outer allocation output input ≤ outerBound allocation)
    (innerBounded : ∀ allocation input, ∑' output, inner allocation output input ≤ innerBound allocation)
    (outerBoundNonnegative : ∀ allocation, 0 ≤ outerBound allocation) (input : ℤ) :
    Summable (fun output => allocatedWeight moment outer inner output input) ∧
      (∑' output : ℤ, allocatedWeight moment outer inner output input) ≤ allocatedBound moment outerBound innerBound := by
  have each (allocation : ℕ) : Summable (fun output => ∑' middle : ℤ,
      outer allocation output middle * inner (moment - allocation) middle input) ∧
      (∑' output : ℤ, ∑' middle : ℤ,
        outer allocation output middle * inner (moment - allocation) middle input) ≤
          outerBound allocation * innerBound (moment - allocation) := by
    have result := Countable.row_product_summable
      (fun input middle => inner (moment - allocation) middle input)
      (fun middle output => outer allocation output middle)
      (innerBound (moment - allocation)) (outerBound allocation)
      (fun input middle => innerNonnegative _ middle input)
      (fun middle output => outerNonnegative _ output middle)
      (innerColumns (moment - allocation)) (outerColumns allocation)
      (innerBounded (moment - allocation)) (outerBounded allocation) (outerBoundNonnegative allocation) input
    simpa only [mul_comm] using result.2
  exact finite_weighted_summability (Finset.range (moment + 1)) (fun allocation => (moment.choose allocation : ℝ))
    (fun allocation => outerBound allocation * innerBound (moment - allocation))
    (fun allocation output => ∑' middle : ℤ, outer allocation output middle * inner (moment - allocation) middle input)
    (fun _ _ => Nat.cast_nonneg _) (fun allocation _ => (each allocation).1)
    (fun allocation _ => (each allocation).2)

end Grad.RepresentedKernel.Composition.Moments
