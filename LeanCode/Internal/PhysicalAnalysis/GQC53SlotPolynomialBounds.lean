import GQC52InversePolynomial

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.InverseAllocation

theorem identity_forcing_sameGrade {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) (slot : RegularitySlot grade) :
    slotNorm (coefficientComposition admissible grade coefficient
      (gradedIdentityCoefficient L sigma gamma ell grade dimension)) slot ≤ splitCeiling grade * ‖coefficient‖ := by
  have productBound := Grad.GaugeCoefficients.Neumann.Regularity.slotComposition_norm_le admissible grade
    coefficient (gradedIdentityCoefficient L sigma gamma ell grade dimension) slot
  rw [slotCompositionNormMajorant_eq_split] at productBound
  apply productBound.trans
  calc
    _ ≤ ∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ) * ‖coefficient‖ := by
      apply Finset.sum_le_sum
      intro split _
      have term := mul_le_mul (slotNorm_le_norm coefficient (lowerRegularitySlot split))
        (identity_slotNorm_le L sigma gamma ell dimension grade (upperRegularitySlot split))
        (slotNorm_nonnegative _ _) (norm_nonneg coefficient)
      rw [mul_one] at term
      exact (mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left term (Nat.cast_nonneg _))
    _ = (∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ)) * ‖coefficient‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (split_sum_le_ceiling slot) (norm_nonneg coefficient)

theorem positive_interaction_sameGrade {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (coefficient deviation : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot → slotNorm deviation other ≤ bound) :
    positiveInteraction coefficient deviation slot ≤ splitCeiling grade * ‖coefficient‖ * bound := by
  classical
  calc
    _ ≤ ∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ) * (‖coefficient‖ * bound) := by
      apply Finset.sum_le_sum
      intro split _
      by_cases same : split = zeroRegularitySlotSplit slot
      · simp only [if_pos same]
        positivity
      · simp only [if_neg same]
        have term := mul_le_mul (slotNorm_le_norm coefficient (lowerRegularitySlot split))
          (lowerBounds (upperRegularitySlot split) (upperSlot_order_lt_of_ne_zeroSplit same))
          (slotNorm_nonnegative _ _) (norm_nonneg coefficient)
        exact (mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left term (Nat.cast_nonneg _))
    _ = (∑ split : RegularitySlotSplit slot, (slotSplitMultiplicity split : ℝ)) * (‖coefficient‖ * bound) := by
      rw [Finset.sum_mul]
    _ ≤ splitCeiling grade * (‖coefficient‖ * bound) :=
      mul_le_mul_of_nonneg_right (split_sum_le_ceiling slot) (mul_nonneg (norm_nonneg coefficient) nonnegative)
    _ = _ := (mul_assoc _ _ _).symm

end Grad.GaugeCoefficients.Physical.Compensated
