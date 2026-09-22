import GC16Slots
import GC16Constants

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Allocation

theorem slotOrder_le_grade {grade : ℕ} (slot : RegularitySlot grade) : slotOrder slot ≤ grade :=
  slot.total_le

theorem coherent_slot_bound {L ell : ℝ} (parameters : PhaseParameters)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon : ℝ)
    {dimension : ℕ}
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (slot : RegularitySlot grade) :
    slotNorm (coefficient grade) slot ≤ coefficientCeiling constants grade *
      physicalBudget parameters field rho epsilon (offset + slotOrder slot) :=
  ((coherent_slotNorm_le coefficient coherent slot).trans (bounds _)).trans
    (mul_le_mul_of_nonneg_right (coefficient_le_ceiling constants nonnegative (slotOrder_le_grade slot))
      (physicalBudget_nonnegative _ _ _ _ _))

theorem identity_forcing_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon : ℝ)
    {dimension : ℕ}
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (slot : RegularitySlot grade) :
    slotNorm (coefficientComposition admissible grade (coefficient grade)
      (gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension)) slot ≤
        forcingConstant constants grade *
          physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
  have productBound := Grad.GaugeCoefficients.Neumann.Regularity.slotComposition_norm_le admissible grade
    (coefficient grade) (gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) slot
  rw [slotCompositionNormMajorant_eq_split] at productBound
  apply productBound.trans
  have termBound (split : RegularitySlotSplit slot) :
      slotNorm (coefficient grade) (lowerRegularitySlot split) *
        slotNorm (gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension)
          (upperRegularitySlot split) ≤
        coefficientCeiling constants grade * physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
    have allocated := slotOrder_split split
    calc
      _ ≤ slotNorm (coefficient grade) (lowerRegularitySlot split) * 1 :=
        mul_le_mul_of_nonneg_left (identity_slotNorm_le _ _ _ _ _ _ _) (slotNorm_nonnegative _ _)
      _ = slotNorm (coefficient grade) (lowerRegularitySlot split) := mul_one _
      _ ≤ coefficientCeiling constants grade *
          physicalBudget parameters field rho epsilon (offset + slotOrder (lowerRegularitySlot split)) :=
        coherent_slot_bound parameters offset grade field rho epsilon coefficient coherent constants nonnegative bounds _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters field rho epsilon (by omega))
        (coefficientCeiling_nonnegative constants nonnegative grade)
  calc
    slotCompositionSplitMajorant (coefficient grade)
        (gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) slot ≤
      ∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ) *
        (coefficientCeiling constants grade *
          physicalBudget parameters field rho epsilon (offset + slotOrder slot)) := by
      apply Finset.sum_le_sum
      intro split _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (termBound split) (Nat.cast_nonneg _)
    _ = (∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ)) *
        (coefficientCeiling constants grade *
          physicalBudget parameters field rho epsilon (offset + slotOrder slot)) := by rw [Finset.sum_mul]
    _ ≤ splitCeiling grade * (coefficientCeiling constants grade *
        physicalBudget parameters field rho epsilon (offset + slotOrder slot)) :=
      mul_le_mul_of_nonneg_right (split_sum_le_ceiling slot)
        (mul_nonneg (coefficientCeiling_nonnegative constants nonnegative grade) (physicalBudget_nonnegative _ _ _ _ _))
    _ = _ := by unfold forcingConstant; ring

def positiveInteraction {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (coefficient deviation : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) : ℝ :=
  ∑ split : RegularitySlotSplit slot,
    if split = zeroRegularitySlotSplit slot then 0 else
      (slotSplitMultiplicity split : ℝ) * slotNorm coefficient (lowerRegularitySlot split) *
        slotNorm deviation (upperRegularitySlot split)

theorem slot_product_zero_split {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (coefficient deviation : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    slotCompositionSplitMajorant coefficient deviation slot =
      slotNorm coefficient (zeroRegularitySlot grade) * slotNorm deviation slot +
        positiveInteraction coefficient deviation slot := by
  unfold slotCompositionSplitMajorant positiveInteraction
  let term : RegularitySlotSplit slot → ℝ := fun split =>
    (slotSplitMultiplicity split : ℝ) * slotNorm coefficient (lowerRegularitySlot split) *
      slotNorm deviation (upperRegularitySlot split)
  change (∑ split, term split) = _ + ∑ split, if split = zeroRegularitySlotSplit slot then 0 else term split
  have splitSum : (∑ split, term split) =
      (∑ split, if split = zeroRegularitySlotSplit slot then term split else 0) +
        ∑ split, if split = zeroRegularitySlotSplit slot then 0 else term split := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro split _
    by_cases same : split = zeroRegularitySlotSplit slot <;> simp [same]
  rw [splitSum]
  simp [term]

theorem positive_interaction_bound {L ell : ℝ} (parameters : PhaseParameters)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon lowBound : ℝ)
    (lowNonnegative : 0 ≤ lowBound)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    {dimension : ℕ}
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (deviation : Coefficient L parameters.sigma0 parameters.gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) (inductionConstant : ℝ) (inductionNonnegative : 0 ≤ inductionConstant)
    (lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot →
      slotNorm deviation other ≤ inductionConstant *
        physicalBudget parameters field rho epsilon (offset + slotOrder other)) :
    positiveInteraction (coefficient grade) deviation slot ≤
      interactionConstant constants offset grade lowBound * inductionConstant *
        physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
  have coefficientNonnegative := coefficientCeiling_nonnegative constants nonnegative grade
  have pairNonnegative := pairCeiling_nonnegative offset grade lowNonnegative
  have termBound (split : RegularitySlotSplit slot) (different : split ≠ zeroRegularitySlotSplit slot) :
      slotNorm (coefficient grade) (lowerRegularitySlot split) *
        slotNorm deviation (upperRegularitySlot split) ≤
      coefficientCeiling constants grade * inductionConstant * pairCeiling offset grade lowBound *
        physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
    have lowerBound := coherent_slot_bound parameters offset grade field rho epsilon coefficient coherent
      constants nonnegative bounds (lowerRegularitySlot split)
    have upperBound := lowerBounds (upperRegularitySlot split) (upperSlot_order_lt_of_ne_zeroSplit different)
    have pairBound := physical_budget_pair offset (slotOrder slot)
      (slotOrder (lowerRegularitySlot split)) (slotOrder (upperRegularitySlot split))
      (le_of_eq (slotOrder_split split)) parameters field rho epsilon lowBound lowNonnegative low
    calc
      _ ≤ (coefficientCeiling constants grade *
          physicalBudget parameters field rho epsilon (offset + slotOrder (lowerRegularitySlot split))) *
          (inductionConstant *
            physicalBudget parameters field rho epsilon (offset + slotOrder (upperRegularitySlot split))) :=
        mul_le_mul lowerBound upperBound (slotNorm_nonnegative _ _)
          (mul_nonneg coefficientNonnegative (physicalBudget_nonnegative _ _ _ _ _))
      _ = (coefficientCeiling constants grade * inductionConstant) *
          (physicalBudget parameters field rho epsilon (offset + slotOrder (lowerRegularitySlot split)) *
            physicalBudget parameters field rho epsilon (offset + slotOrder (upperRegularitySlot split))) := by ring
      _ ≤ (coefficientCeiling constants grade * inductionConstant) *
          (pairBudgetConstant offset (slotOrder slot) lowBound *
            physicalBudget parameters field rho epsilon (offset + slotOrder slot)) :=
        mul_le_mul_of_nonneg_left pairBound (mul_nonneg coefficientNonnegative inductionNonnegative)
      _ ≤ (coefficientCeiling constants grade * inductionConstant) *
          (pairCeiling offset grade lowBound *
            physicalBudget parameters field rho epsilon (offset + slotOrder slot)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pair_le_ceiling offset lowNonnegative (slotOrder_le_grade slot))
            (physicalBudget_nonnegative _ _ _ _ _))
          (mul_nonneg coefficientNonnegative inductionNonnegative)
      _ = _ := by ring
  let total := coefficientCeiling constants grade * inductionConstant * pairCeiling offset grade lowBound *
    physicalBudget parameters field rho epsilon (offset + slotOrder slot)
  have totalNonnegative : 0 ≤ total :=
    mul_nonneg (mul_nonneg (mul_nonneg coefficientNonnegative inductionNonnegative) pairNonnegative)
      (physicalBudget_nonnegative _ _ _ _ _)
  calc
    positiveInteraction (coefficient grade) deviation slot ≤
        ∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ) * total := by
      apply Finset.sum_le_sum
      intro split _
      by_cases same : split = zeroRegularitySlotSplit slot
      · simp only [same, ite_true]
        exact mul_nonneg (Nat.cast_nonneg _) totalNonnegative
      · simp only [same, ite_false]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (termBound split same) (Nat.cast_nonneg _)
    _ = (∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ)) * total := by
      rw [Finset.sum_mul]
    _ ≤ splitCeiling grade * total := mul_le_mul_of_nonneg_right (split_sum_le_ceiling slot) totalNonnegative
    _ = _ := by unfold total interactionConstant forcingConstant; ring

end Grad.GaugeCoefficients.Physical.InverseAllocation
