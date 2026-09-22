import GC12Recurrence

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

def slotSplitEquiv {grade : ℕ} {slot : RegularitySlot grade} :
    RegularitySlotSplit slot ≃
      DerivativeSplit (slotDerivativeIndex slot) ×
        Fin ((slot.moment : ℕ) + 1) where
  toFun split := (slotPhysicalSplit split, split.moment)
  invFun pair := combineSlotSplit pair.1 pair.2
  left_inv split := by
    cases split
    rfl
  right_inv pair := by
    cases pair
    rfl

def slotCompositionSplitMajorant {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) : ℝ :=
  ∑ split : RegularitySlotSplit slot,
    (slotSplitMultiplicity split : ℝ) *
      slotNorm outer (lowerRegularitySlot split) *
        slotNorm inner (upperRegularitySlot split)

theorem slotCompositionNormMajorant_eq_split {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    slotCompositionNormMajorant outer inner slot =
      slotCompositionSplitMajorant outer inner slot := by
  unfold slotCompositionNormMajorant slotCompositionSplitMajorant
  change (∑ physical : DerivativeSplit (slotDerivativeIndex slot),
      ∑ moment : Fin ((slot.moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) *
          slotNorm outer (lowerRegularitySlot
            (combineSlotSplit physical moment)) *
          slotNorm inner (upperRegularitySlot
            (combineSlotSplit physical moment))) = _
  rw [← Fintype.sum_prod_type (fun pair :
    DerivativeSplit (slotDerivativeIndex slot) ×
      Fin ((slot.moment : ℕ) + 1) =>
        (slotSplitMultiplicity (combineSlotSplit pair.1 pair.2) : ℝ) *
          slotNorm outer (lowerRegularitySlot
            (combineSlotSplit pair.1 pair.2)) *
          slotNorm inner (upperRegularitySlot
            (combineSlotSplit pair.1 pair.2)))]
  symm
  apply Fintype.sum_equiv slotSplitEquiv
  intro split
  rfl

def zeroRegularitySlotSplit {grade : ℕ} (slot : RegularitySlot grade) :
    RegularitySlotSplit slot where
  first := ⟨0, by omega⟩
  second := ⟨0, by omega⟩
  moment := ⟨0, by omega⟩

theorem regularitySlot_ext {grade : ℕ} {left right : RegularitySlot grade}
    (first : left.first = right.first) (second : left.second = right.second)
    (moment : left.moment = right.moment) : left = right := by
  cases left
  cases right
  simp_all

theorem regularitySlotSplit_ext {grade : ℕ} {slot : RegularitySlot grade}
    {left right : RegularitySlotSplit slot}
    (first : left.first = right.first) (second : left.second = right.second)
    (moment : left.moment = right.moment) : left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem lowerRegularitySlot_zeroSplit {grade : ℕ}
    (slot : RegularitySlot grade) :
    lowerRegularitySlot (zeroRegularitySlotSplit slot) =
      zeroRegularitySlot grade := by
  apply regularitySlot_ext <;> apply Fin.ext <;> rfl

@[simp] theorem upperRegularitySlot_zeroSplit {grade : ℕ}
    (slot : RegularitySlot grade) :
    upperRegularitySlot (zeroRegularitySlotSplit slot) = slot := by
  apply regularitySlot_ext <;> apply Fin.ext <;>
    simp [upperRegularitySlot, zeroRegularitySlotSplit]

@[simp] theorem slotSplitMultiplicity_zeroSplit {grade : ℕ}
    (slot : RegularitySlot grade) :
    slotSplitMultiplicity (zeroRegularitySlotSplit slot) = 1 := by
  simp [slotSplitMultiplicity, zeroRegularitySlotSplit]

theorem regularitySlot_eq_zero_of_order_eq_zero {grade : ℕ}
    {slot : RegularitySlot grade} (orderZero : slotOrder slot = 0) :
    slot = zeroRegularitySlot grade := by
  have firstZero : (slot.first : ℕ) = 0 := by
    simp only [slotOrder] at orderZero
    omega
  have secondZero : (slot.second : ℕ) = 0 := by
    simp only [slotOrder] at orderZero
    omega
  have momentZero : (slot.moment : ℕ) = 0 := by
    simp only [slotOrder] at orderZero
    omega
  apply regularitySlot_ext <;> apply Fin.ext
  · exact firstZero
  · exact secondZero
  · exact momentZero

theorem lowerSlot_order_positive_of_ne_zeroSplit {grade : ℕ}
    {slot : RegularitySlot grade} {split : RegularitySlotSplit slot}
    (different : split ≠ zeroRegularitySlotSplit slot) :
    0 < slotOrder (lowerRegularitySlot split) := by
  by_contra notPositive
  have lowerOrderZero : slotOrder (lowerRegularitySlot split) = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  have firstZero : (split.first : ℕ) = 0 := by
    simp only [slotOrder, lowerRegularitySlot] at lowerOrderZero
    omega
  have secondZero : (split.second : ℕ) = 0 := by
    simp only [slotOrder, lowerRegularitySlot] at lowerOrderZero
    omega
  have momentZero : (split.moment : ℕ) = 0 := by
    simp only [slotOrder, lowerRegularitySlot] at lowerOrderZero
    omega
  apply different
  apply regularitySlotSplit_ext <;> apply Fin.ext
  · exact firstZero
  · exact secondZero
  · exact momentZero

theorem upperSlot_order_lt_of_ne_zeroSplit {grade : ℕ}
    {slot : RegularitySlot grade} {split : RegularitySlotSplit slot}
    (different : split ≠ zeroRegularitySlotSplit slot) :
    slotOrder (upperRegularitySlot split) < slotOrder slot := by
  have lowerPositive := lowerSlot_order_positive_of_ne_zeroSplit different
  have orderSplit := slotOrder_split split
  omega

def positiveSplitForcing {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) (power : ℕ) : ℝ :=
  ∑ split : RegularitySlotSplit slot,
    if split = zeroRegularitySlotSplit slot then 0 else
      (slotSplitMultiplicity split : ℝ) *
        slotNorm coefficient (lowerRegularitySlot split) *
          slotNorm (gradedCoefficientPower admissible coefficient power)
            (upperRegularitySlot split)

theorem slotCompositionSplitMajorant_eq_zero_add_forcing
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) (power : ℕ) :
    slotCompositionSplitMajorant coefficient
        (gradedCoefficientPower admissible coefficient power) slot =
      slotNorm coefficient (zeroRegularitySlot grade) *
          slotNorm (gradedCoefficientPower admissible coefficient power) slot +
        positiveSplitForcing admissible coefficient slot power := by
  unfold slotCompositionSplitMajorant positiveSplitForcing
  let term : RegularitySlotSplit slot → ℝ := fun split =>
    (slotSplitMultiplicity split : ℝ) *
      slotNorm coefficient (lowerRegularitySlot split) *
        slotNorm (gradedCoefficientPower admissible coefficient power)
          (upperRegularitySlot split)
  change (∑ split, term split) =
    slotNorm coefficient (zeroRegularitySlot grade) *
        slotNorm (gradedCoefficientPower admissible coefficient power) slot +
      ∑ split, if split = zeroRegularitySlotSplit slot then 0 else term split
  calc
    (∑ split, term split) =
        ∑ split,
          ((if split = zeroRegularitySlotSplit slot then term split else 0) +
            if split = zeroRegularitySlotSplit slot then 0 else term split) := by
      apply Finset.sum_congr rfl
      intro split _membership
      by_cases same : split = zeroRegularitySlotSplit slot <;> simp [same]
    _ = (∑ split,
          if split = zeroRegularitySlotSplit slot then term split else 0) +
        ∑ split,
          if split = zeroRegularitySlotSplit slot then 0 else term split := by
      exact Finset.sum_add_distrib
    _ = _ := by
      simp [term]

theorem positiveSplitForcing_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    ∀ power, 0 ≤ positiveSplitForcing admissible coefficient slot power := by
  intro power
  unfold positiveSplitForcing
  apply Finset.sum_nonneg
  intro split _membership
  by_cases same : split = zeroRegularitySlotSplit slot
  · simp [same]
  · simp only [same, ↓reduceIte]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (slotNorm_nonnegative _ _))
      (slotNorm_nonnegative _ _)

theorem positiveSplitForcing_summable_of_lower_slots
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade)
    (lowerSummable : ∀ other : RegularitySlot grade,
      slotOrder other < slotOrder slot →
        Summable (fun power =>
          slotNorm (gradedCoefficientPower admissible coefficient power) other)) :
    Summable (positiveSplitForcing admissible coefficient slot) := by
  unfold positiveSplitForcing
  apply summable_sum
  intro split _membership
  by_cases same : split = zeroRegularitySlotSplit slot
  · simp [same]
  · simp only [same, ↓reduceIte]
    have upperSummable := lowerSummable (upperRegularitySlot split)
      (upperSlot_order_lt_of_ne_zeroSplit same)
    simpa only [mul_assoc] using upperSummable.mul_left
      ((slotSplitMultiplicity split : ℝ) *
        slotNorm coefficient (lowerRegularitySlot split))

/-- Direct one-high power estimate in summability form.  The zero split is
the frozen base contraction; every other labelled Leibniz split spends at
least one of the finitely many regularity labels, so the recurrence is
triangular in `slotOrder`. -/
theorem gradedCoefficientPower_slotNorm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1)
    (slot : RegularitySlot grade) :
    Summable (fun power =>
      slotNorm (gradedCoefficientPower admissible gradedCoefficient power) slot) := by
  have thetaNonnegative : 0 ≤ theta :=
    (norm_nonneg baseCoefficient).trans normBound
  refine Nat.strong_induction_on
    (p := fun order => ∀ current : RegularitySlot grade,
      slotOrder current = order →
        Summable (fun power =>
          slotNorm (gradedCoefficientPower admissible gradedCoefficient power)
            current))
    (slotOrder slot) ?_ slot rfl
  intro order inductionHypothesis current currentOrder
  by_cases orderZero : order = 0
  · have currentZero : current = zeroRegularitySlot grade :=
      regularitySlot_eq_zero_of_order_eq_zero (currentOrder.trans orderZero)
    subst current
    apply Summable.of_nonneg_of_le
      (fun power => slotNorm_nonnegative _ _)
      (fun power => ?_)
      (summable_geometric_of_lt_one thetaNonnegative thetaLt)
    rw [zeroSlotNorm_eq_baseNorm
      (gradedCoefficientPower_realizes admissible baseCoefficient gradedCoefficient
        realizes power)]
    exact coefficientPower_norm_le_theta admissible positive baseCoefficient theta
      normBound power
  · have currentPositive : 0 < slotOrder current := by omega
    let values : ℕ → ℝ := fun power =>
      slotNorm (gradedCoefficientPower admissible gradedCoefficient power) current
    let forcing : ℕ → ℝ :=
      positiveSplitForcing admissible gradedCoefficient current
    have forcingSummable : Summable forcing := by
      apply positiveSplitForcing_summable_of_lower_slots
      intro other otherLower
      exact inductionHypothesis (slotOrder other)
        (by omega) other rfl
    apply summable_of_geometric_recurrence
      (values := values) (forcing := forcing)
      (fun power => slotNorm_nonnegative _ _)
      (positiveSplitForcing_nonnegative admissible gradedCoefficient current)
      thetaNonnegative thetaLt forcingSummable
    intro power
    calc
      values (power + 1) =
          slotNorm (coefficientComposition admissible grade gradedCoefficient
            (gradedCoefficientPower admissible gradedCoefficient power)) current := by
        rfl
      _ ≤ slotCompositionNormMajorant gradedCoefficient
          (gradedCoefficientPower admissible gradedCoefficient power) current :=
        slotComposition_norm_le admissible grade gradedCoefficient
          (gradedCoefficientPower admissible gradedCoefficient power) current
      _ = slotNorm gradedCoefficient (zeroRegularitySlot grade) * values power +
          forcing power := by
        rw [slotCompositionNormMajorant_eq_split]
        exact slotCompositionSplitMajorant_eq_zero_add_forcing
          admissible gradedCoefficient current power
      _ ≤ theta * values power + forcing power := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right
          · rw [zeroSlotNorm_eq_baseNorm realizes]
            exact normBound
          · exact slotNorm_nonnegative _ _
        · exact le_rfl

end Grad.GaugeCoefficients.Neumann.Regularity
