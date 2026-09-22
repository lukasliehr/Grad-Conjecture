import GC15PhysicalInterpolation

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.CartesianState

/-- Actual AQ2 and the accepted finite allocation theorem give the one-high
product, including arbitrary unused derivative order and zero low sizes. -/
theorem physical_budget_allocated_product {Index : Type*} [Fintype Index] [Nonempty Index]
    (offset grade : ℕ) (gradePositive : 0 < grade)
    (orders : Index → ℕ) (allocated : ∑ index, orders index ≤ grade)
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ) :
    (∏ index, physicalBudget parameters field rho epsilon (offset + orders index)) ≤
      physicalInterpolationConstant offset grade ^ Fintype.card Index *
        physicalBudget parameters field rho epsilon offset ^ (Fintype.card Index - 1) *
          physicalBudget parameters field rho epsilon (offset + grade) := by
  classical
  have orderLe (index : Index) : orders index ≤ grade :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)).trans allocated
  have bound := Grad.TameAllocation.interpolated_product_bound
    (fun index => physicalBudget parameters field rho epsilon (offset + orders index))
    (fun _ => physicalInterpolationConstant offset grade)
    (physicalBudget parameters field rho epsilon offset)
    (physicalBudget parameters field rho epsilon (offset + grade)) orders grade gradePositive allocated
    (physicalBudget_nonnegative _ _ _ _ _)
    (physicalBudget_monotone parameters field rho epsilon (by omega))
    (fun _ => physicalBudget_nonnegative _ _ _ _ _)
    (fun _ => zero_le_one.trans (physicalInterpolationConstant_one_le offset grade))
    (fun index => physical_budget_interpolation offset grade (orders index) gradePositive
      (orderLe index) parameters field rho epsilon)
  simpa only [Finset.prod_const, Finset.card_univ] using bound

def pairBudgetConstant (offset grade : ℕ) (lowBound : ℝ) : ℝ :=
  physicalInterpolationConstant offset grade ^ 2 * (lowBound + 1)

theorem pairBudgetConstant_nonnegative (offset grade : ℕ) {lowBound : ℝ} (lowNonnegative : 0 ≤ lowBound) :
    0 ≤ pairBudgetConstant offset grade lowBound := by
  unfold pairBudgetConstant
  positivity

theorem physical_budget_pair (offset grade first second : ℕ) (allocated : first + second ≤ grade)
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon lowBound : ℝ)
    (lowNonnegative : 0 ≤ lowBound)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound) :
    physicalBudget parameters field rho epsilon (offset + first) *
      physicalBudget parameters field rho epsilon (offset + second) ≤
        pairBudgetConstant offset grade lowBound *
          physicalBudget parameters field rho epsilon (offset + grade) := by
  have budgetNonnegative := physicalBudget_nonnegative parameters field rho epsilon offset
  have constantNonnegative : 0 ≤ physicalInterpolationConstant offset grade ^ 2 := sq_nonneg _
  have constantOne : 1 ≤ physicalInterpolationConstant offset grade ^ 2 :=
    one_le_pow₀ (physicalInterpolationConstant_one_le offset grade)
  have lowConstant : lowBound ≤ pairBudgetConstant offset grade lowBound := by
    unfold pairBudgetConstant
    exact (le_add_of_nonneg_right zero_le_one).trans
      (le_mul_of_one_le_left (by linarith) constantOne)
  by_cases gradeZero : grade = 0
  · have firstZero : first = 0 := by omega
    have secondZero : second = 0 := by omega
    simp only [gradeZero, firstZero, secondZero, Nat.add_zero]
    exact (mul_le_mul_of_nonneg_right low budgetNonnegative).trans
      (mul_le_mul_of_nonneg_right (by simpa [gradeZero] using lowConstant) budgetNonnegative)
  have gradePositive : 0 < grade := by omega
  have product := physical_budget_allocated_product offset grade gradePositive
    (![first, second] : Fin 2 → ℕ) (by simpa [Fin.sum_univ_succ] using allocated)
    parameters field rho epsilon
  have product' : physicalBudget parameters field rho epsilon (offset + first) *
      physicalBudget parameters field rho epsilon (offset + second) ≤
      physicalInterpolationConstant offset grade ^ 2 *
        physicalBudget parameters field rho epsilon offset *
          physicalBudget parameters field rho epsilon (offset + grade) := by
    simpa [Fin.prod_univ_succ] using product
  exact product'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (low.trans (le_add_of_nonneg_right zero_le_one)) constantNonnegative)
    (physicalBudget_nonnegative _ _ _ _ _))

end Grad.GaugeCoefficients.Physical.Allocation
