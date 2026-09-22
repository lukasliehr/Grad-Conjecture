import GC15RectangularSlots

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def slotIndexAtOrder {grade : ℕ} (slot : RegularitySlot grade) :
    DerivativeIndex (slotOrder slot) :=
  ⟨(⟨slot.first, by simp only [slotOrder]; omega⟩,
      ⟨slot.second, by simp only [slotOrder]; omega⟩), by simp only [slotOrder]; omega⟩

theorem coherent_slotCoordinate {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (slot : RegularitySlot grade) (cell : ℤ) :
    slotCoordinate (family grade) slot cell =
      weightedDerivative (family (slotOrder slot)) cell (slotIndexAtOrder slot) := by
  apply ContinuousMap.ext
  intro point
  rw [slotCoordinate_apply, weighted_derivative_literal]
  rw [coherent grade (slotOrder slot) (slotDerivativeIndex slot) (slotIndexAtOrder slot) rfl cell point]
  congr 2
  unfold coefficientScale
  congr 2
  simp only [slotOrder, derivativeOrder, slotIndexAtOrder]
  omega

theorem coherent_slotNorm_le {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (slot : RegularitySlot grade) :
    slotNorm (family grade) slot ≤ ‖family (slotOrder slot)‖ := by
  unfold slotNorm
  simp_rw [coherent_slotCoordinate family coherent]
  exact coordinate_norm_sum_le (family (slotOrder slot)).val (slotIndexAtOrder slot)

def topSlot {grade : ℕ} (index : DerivativeIndex grade) : RegularitySlot grade where
  first := index.val.1
  second := index.val.2
  moment := ⟨grade - derivativeOrder index, by omega⟩
  total_le := by
    have bound := index.property
    change (index.val.1 : ℕ) + (index.val.2 : ℕ) + (grade - derivativeOrder index) ≤ grade
    unfold derivativeOrder
    omega

theorem topSlot_order {grade : ℕ} (index : DerivativeIndex grade) : slotOrder (topSlot index) = grade := by
  have bound := index.property
  simp only [slotOrder, topSlot, derivativeOrder]
  omega

theorem topSlot_derivative {grade : ℕ} (index : DerivativeIndex grade) :
    slotDerivativeIndex (topSlot index) = index := by
  apply Subtype.ext
  rfl

theorem topSlotCoordinate {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (index : DerivativeIndex grade) (cell : ℤ) :
    slotCoordinate coefficient (topSlot index) cell = weightedDerivative coefficient cell index := by
  unfold slotCoordinate slotGap
  rw [topSlot_order, Nat.sub_self, pow_zero, inv_one, one_smul, topSlot_derivative]

theorem norm_eq_topSlot_sum {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) :
    ‖coefficient‖ = ∑ index : DerivativeIndex grade, slotNorm coefficient (topSlot index) := by
  rw [coefficient_norm_formula]
  unfold slotNorm
  simp_rw [topSlotCoordinate]
  exact Summable.tsum_finsetSum (fun index _ => coordinate_norm_summable coefficient.val index)

def allocatedProductConstant (grade : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade,
    ∑ physical : DerivativeSplit (slotDerivativeIndex (topSlot index)),
      ∑ moment : Fin (((topSlot index).moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ)

theorem allocatedProductConstant_nonnegative (grade : ℕ) : 0 ≤ allocatedProductConstant grade := by
  unfold allocatedProductConstant
  positivity

theorem allocated_composition_norm {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {input middle output : ℕ}
    (outer : CoefficientFamily L sigma gamma ell middle output)
    (inner : CoefficientFamily L sigma gamma ell input middle)
    (outerCoherent : FamilyCoherent outer) (innerCoherent : FamilyCoherent inner) :
    ‖coefficientComposition admissible grade (outer grade) (inner grade)‖ ≤
      allocatedProductConstant grade *
        ∑ order : Fin (grade + 1), ‖outer order.val‖ * ‖inner (grade - order.val)‖ := by
  let total := ∑ order : Fin (grade + 1), ‖outer order.val‖ * ‖inner (grade - order.val)‖
  have splitBound (index : DerivativeIndex grade)
      (physical : DerivativeSplit (slotDerivativeIndex (topSlot index)))
      (moment : Fin (((topSlot index).moment : ℕ) + 1)) :
      slotNorm (outer grade) (lowerRegularitySlot (combineSlotSplit physical moment)) *
        slotNorm (inner grade) (upperRegularitySlot (combineSlotSplit physical moment)) ≤ total := by
    let split := combineSlotSplit physical moment
    have orderSum : slotOrder (lowerRegularitySlot split) + slotOrder (upperRegularitySlot split) = grade := by
      rw [slotOrder_split, topSlot_order]
    have lowerLe : slotOrder (lowerRegularitySlot split) ≤ grade := by omega
    have upperEquality : slotOrder (upperRegularitySlot split) = grade - slotOrder (lowerRegularitySlot split) := by omega
    have single := Finset.single_le_sum
      (f := fun order : Fin (grade + 1) => ‖outer order.val‖ * ‖inner (grade - order.val)‖)
      (s := Finset.univ) (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Finset.mem_univ (⟨slotOrder (lowerRegularitySlot split), by omega⟩ : Fin (grade + 1)))
    change slotNorm (outer grade) (lowerRegularitySlot split) *
      slotNorm (inner grade) (upperRegularitySlot split) ≤ total
    calc
      _ ≤ ‖outer (slotOrder (lowerRegularitySlot split))‖ *
          ‖inner (slotOrder (upperRegularitySlot split))‖ :=
        mul_le_mul (coherent_slotNorm_le outer outerCoherent _)
          (coherent_slotNorm_le inner innerCoherent _) (slotNorm_nonnegative _ _) (norm_nonneg _)
      _ ≤ total := by rw [upperEquality]; exact single
  calc
    _ = ∑ index : DerivativeIndex grade,
        slotNorm (coefficientComposition admissible grade (outer grade) (inner grade)) (topSlot index) :=
      norm_eq_topSlot_sum _
    _ ≤ ∑ index : DerivativeIndex grade,
        slotCompositionNormMajorant (outer grade) (inner grade) (topSlot index) := by
      apply Finset.sum_le_sum
      intro index _
      exact slotComposition_norm_le admissible grade (outer grade) (inner grade) (topSlot index)
    _ ≤ ∑ index : DerivativeIndex grade,
        ∑ physical : DerivativeSplit (slotDerivativeIndex (topSlot index)),
          ∑ moment : Fin (((topSlot index).moment : ℕ) + 1),
            (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) * total := by
      apply Finset.sum_le_sum
      intro index _
      unfold slotCompositionNormMajorant
      apply Finset.sum_le_sum
      intro physical _
      apply Finset.sum_le_sum
      intro moment _
      dsimp only
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (splitBound index physical moment) (Nat.cast_nonneg _)
    _ = _ := by
      unfold allocatedProductConstant
      simp only [Finset.sum_mul]
      rfl

theorem allocatedCompositionGoal : AllocatedCompositionGoal := by
  intro grade
  refine ⟨allocatedProductConstant grade, allocatedProductConstant_nonnegative grade, ?_⟩
  intro L sigma gamma ell admissible input middle output outer inner outerCoherent innerCoherent
  exact allocated_composition_norm admissible grade outer inner outerCoherent innerCoherent

end Grad.GaugeCoefficients.Physical.Allocation
