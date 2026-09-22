import GC16Interface

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation

def coefficientCeiling (constants : ℕ → ℝ) (grade : ℕ) : ℝ :=
  ∑ order : Fin (grade + 1), constants order.val

def splitCeiling (grade : ℕ) : ℝ :=
  ∑ slot : RegularitySlot grade, ∑ split : RegularitySlotSplit slot,
    (slotSplitMultiplicity split : ℝ)

def pairCeiling (offset grade : ℕ) (lowBound : ℝ) : ℝ :=
  ∑ order : Fin (grade + 1), pairBudgetConstant offset order.val lowBound

theorem coefficientCeiling_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (grade : ℕ) :
    0 ≤ coefficientCeiling constants grade := Finset.sum_nonneg fun _ _ => nonnegative _

theorem coefficient_le_ceiling (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) {grade order : ℕ} (bounded : order ≤ grade) :
    constants order ≤ coefficientCeiling constants grade := by
  unfold coefficientCeiling
  exact Finset.single_le_sum (f := fun index : Fin (grade + 1) => constants index.val)
    (fun _ _ => nonnegative _) (Finset.mem_univ (⟨order, by omega⟩ : Fin (grade + 1)))

theorem splitCeiling_nonnegative (grade : ℕ) : 0 ≤ splitCeiling grade := by
  unfold splitCeiling
  positivity

theorem split_sum_le_ceiling {grade : ℕ} (slot : RegularitySlot grade) :
    (∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ)) ≤ splitCeiling grade := by
  unfold splitCeiling
  exact Finset.single_le_sum
    (f := fun slot : RegularitySlot grade => ∑ split : RegularitySlotSplit slot,
      (slotSplitMultiplicity split : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    (Finset.mem_univ slot)

theorem pairCeiling_nonnegative (offset grade : ℕ) {lowBound : ℝ} (nonnegative : 0 ≤ lowBound) :
    0 ≤ pairCeiling offset grade lowBound :=
  Finset.sum_nonneg fun _ _ => pairBudgetConstant_nonnegative _ _ nonnegative

theorem pair_le_ceiling (offset : ℕ) {grade order : ℕ} {lowBound : ℝ}
    (nonnegative : 0 ≤ lowBound) (bounded : order ≤ grade) :
    pairBudgetConstant offset order lowBound ≤ pairCeiling offset grade lowBound := by
  unfold pairCeiling
  exact Finset.single_le_sum (f := fun index : Fin (grade + 1) => pairBudgetConstant offset index.val lowBound)
    (fun _ _ => pairBudgetConstant_nonnegative _ _ nonnegative)
    (Finset.mem_univ (⟨order, by omega⟩ : Fin (grade + 1)))

def forcingConstant (constants : ℕ → ℝ) (grade : ℕ) : ℝ :=
  coefficientCeiling constants grade * splitCeiling grade

def interactionConstant (constants : ℕ → ℝ) (offset grade : ℕ) (lowBound : ℝ) : ℝ :=
  forcingConstant constants grade * pairCeiling offset grade lowBound

theorem forcingConstant_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (grade : ℕ) :
    0 ≤ forcingConstant constants grade :=
  mul_nonneg (coefficientCeiling_nonnegative constants nonnegative grade) (splitCeiling_nonnegative grade)

theorem interactionConstant_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (offset grade : ℕ)
    {lowBound : ℝ} (lowNonnegative : 0 ≤ lowBound) :
    0 ≤ interactionConstant constants offset grade lowBound :=
  mul_nonneg (forcingConstant_nonnegative constants nonnegative grade)
    (pairCeiling_nonnegative offset grade lowNonnegative)

/-- Finite induction constants only. All occurrences of the inverse are
absorbed with the same fixed factor 1/(1-theta). -/
def inverseSlotConstant (constants : ℕ → ℝ) (offset grade : ℕ) (lowBound theta : ℝ) (order : ℕ) : ℝ :=
  Nat.rec 0 (fun _ previous =>
    (forcingConstant constants grade +
      interactionConstant constants offset grade lowBound * previous) / (1 - theta) + previous) order

theorem inverseSlotConstant_zero (constants : ℕ → ℝ) (offset grade : ℕ) (lowBound theta : ℝ) :
    inverseSlotConstant constants offset grade lowBound theta 0 = 0 := rfl

theorem inverseSlotConstant_succ (constants : ℕ → ℝ) (offset grade : ℕ) (lowBound theta : ℝ) (order : ℕ) :
    inverseSlotConstant constants offset grade lowBound theta (order + 1) =
      (forcingConstant constants grade + interactionConstant constants offset grade lowBound *
        inverseSlotConstant constants offset grade lowBound theta order) / (1 - theta) +
          inverseSlotConstant constants offset grade lowBound theta order := rfl

theorem inverseSlotConstant_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (offset grade : ℕ)
    {lowBound theta : ℝ} (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1) (order : ℕ) :
    0 ≤ inverseSlotConstant constants offset grade lowBound theta order := by
  induction order with
  | zero => exact le_refl 0
  | succ order ih =>
    rw [inverseSlotConstant_succ]
    exact add_nonneg (div_nonneg
      (add_nonneg (forcingConstant_nonnegative constants nonnegative grade)
        (mul_nonneg (interactionConstant_nonnegative constants nonnegative offset grade lowNonnegative) ih))
      (by linarith)) ih

theorem inverseSlotConstant_monotone (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (offset grade : ℕ)
    {lowBound theta : ℝ} (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1) :
    Monotone (inverseSlotConstant constants offset grade lowBound theta) := by
  apply monotone_nat_of_le_succ
  intro order
  rw [inverseSlotConstant_succ]
  apply le_add_of_nonneg_left
  exact div_nonneg
    (add_nonneg (forcingConstant_nonnegative constants nonnegative grade)
      (mul_nonneg (interactionConstant_nonnegative constants nonnegative offset grade lowNonnegative)
        (inverseSlotConstant_nonnegative constants nonnegative offset grade lowNonnegative thetaLt order)))
    (by linarith)

end Grad.GaugeCoefficients.Physical.InverseAllocation
