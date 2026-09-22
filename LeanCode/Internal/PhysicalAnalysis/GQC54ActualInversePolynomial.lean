import GQC53SlotPolynomialBounds

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem finite_real_sum_const {Index : Type*} [Fintype Index] (value : ℝ) :
    (∑ _index : Index, value) = (Fintype.card Index : ℝ) * value := by simp

theorem inverse_slot_polynomial_step {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension) (coherent : FamilyCoherent coefficient)
    (small : ‖coefficient 0‖ ≤ 1 / 2) (slot : RegularitySlot grade)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot →
      slotNorm (inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension) other ≤ bound) :
    slotNorm (inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension) slot ≤
      2 * splitCeiling grade * ‖coefficient grade‖ * (1 + bound) := by
  let identity := gradedIdentityCoefficient L sigma gamma ell grade dimension
  let deviation := inverseFamily admissible coefficient grade - identity
  have fixed := inverse_deviation_fixedPoint admissible positive coefficient coherent (1 / 2) small (by norm_num) (grade := grade)
  have triangle : slotNorm deviation slot ≤ slotNorm (coefficientComposition admissible grade (coefficient grade) identity) slot +
      slotNorm (coefficientComposition admissible grade (coefficient grade) deviation) slot :=
    (congrArg (fun value => slotNorm value slot) fixed).trans_le (slotNorm_add_le _ _ slot)
  have forcing := identity_forcing_sameGrade admissible (coefficient grade) slot
  have product := Grad.GaugeCoefficients.Neumann.Regularity.slotComposition_norm_le admissible grade
    (coefficient grade) deviation slot
  rw [slotCompositionNormMajorant_eq_split, slot_product_zero_split,
    coherent_zero_slot_norm coefficient coherent] at product
  have interaction := positive_interaction_sameGrade (coefficient grade) deviation slot bound nonnegative lowerBounds
  have zeroTerm := mul_le_mul_of_nonneg_right small (slotNorm_nonnegative deviation slot)
  have combined := triangle.trans (add_le_add forcing
    (product.trans (add_le_add zeroTerm interaction)))
  nlinarith

theorem inverse_slot_polynomial_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension) (coherent : FamilyCoherent coefficient)
    (small : ‖coefficient 0‖ ≤ 1 / 2) (slot : RegularitySlot grade) :
    slotNorm (inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension) slot ≤
      (inverseSlotPolynomial grade (slotOrder slot + 1)).eval ‖coefficient grade‖ := by
  have inductionStatement : ∀ order : ℕ, ∀ slot : RegularitySlot grade, slotOrder slot = order →
      slotNorm (inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension) slot ≤
        (inverseSlotPolynomial grade (order + 1)).eval ‖coefficient grade‖ := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro slot same
      have lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot →
          slotNorm (inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension) other ≤
            (inverseSlotPolynomial grade order).eval ‖coefficient grade‖ := by
        intro other smaller
        have ltOrder : slotOrder other < order := by omega
        exact (ih (slotOrder other) ltOrder other rfl).trans
          (inverseSlotPolynomial_eval_monotone_order grade (norm_nonneg _) (by omega : slotOrder other + 1 ≤ order))
      have step := inverse_slot_polynomial_step admissible positive coefficient coherent small slot
        ((inverseSlotPolynomial grade order).eval ‖coefficient grade‖)
        (inverseSlotPolynomial_eval_nonnegative grade order (norm_nonneg _)) lowerBounds
      rw [inverseSlotPolynomial_eval_succ]
      exact step.trans (le_add_of_nonneg_right (inverseSlotPolynomial_eval_nonnegative grade order (norm_nonneg _)))
  exact inductionStatement (slotOrder slot) slot rfl

/-- A genuine finite polynomial bound for the already constructed inverse,
at its own coefficient grade; no larger physical B-budget is substituted. -/
theorem inverse_deviation_polynomial_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension) (coherent : FamilyCoherent coefficient)
    (small : ‖coefficient 0‖ ≤ 1 / 2) (grade : ℕ) :
    ‖inverseFamily admissible coefficient grade - gradedIdentityCoefficient L sigma gamma ell grade dimension‖ ≤
      (Fintype.card (DerivativeIndex grade) : ℝ) * (inverseSlotPolynomial grade (grade + 1)).eval ‖coefficient grade‖ := by
  rw [coefficient_norm_eq_sum_topSlots]
  calc
    _ ≤ ∑ _index : DerivativeIndex grade, (inverseSlotPolynomial grade (grade + 1)).eval ‖coefficient grade‖ := by
      apply Finset.sum_le_sum
      intro index _
      have bound := inverse_slot_polynomial_bound admissible positive coefficient coherent small (topRegularitySlot index)
      exact bound.trans_eq (congrArg
        (fun order : ℕ => (inverseSlotPolynomial grade (order + 1)).eval ‖coefficient grade‖)
        (slotOrder_top index))
    _ = _ := finite_real_sum_const _

end Grad.GaugeCoefficients.Physical.Compensated
