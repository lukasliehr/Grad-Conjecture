import GC12Slots

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

/-- A simultaneous Leibniz split of the two Cartesian labels and the
polynomial cell-moment labels. -/
structure RegularitySlotSplit {grade : ℕ} (slot : RegularitySlot grade) where
  first : Fin ((slot.first : ℕ) + 1)
  second : Fin ((slot.second : ℕ) + 1)
  moment : Fin ((slot.moment : ℕ) + 1)
deriving Fintype, DecidableEq

def slotPhysicalSplit {grade : ℕ} {slot : RegularitySlot grade}
    (split : RegularitySlotSplit slot) : DerivativeSplit (slotDerivativeIndex slot) :=
  (split.first, split.second)

def lowerRegularitySlot {grade : ℕ} {slot : RegularitySlot grade}
    (split : RegularitySlotSplit slot) : RegularitySlot grade := by
  have firstLe : (split.first : ℕ) ≤ (slot.first : ℕ) :=
    Nat.lt_succ_iff.mp split.first.isLt
  have secondLe : (split.second : ℕ) ≤ (slot.second : ℕ) :=
    Nat.lt_succ_iff.mp split.second.isLt
  have momentLe : (split.moment : ℕ) ≤ (slot.moment : ℕ) :=
    Nat.lt_succ_iff.mp split.moment.isLt
  refine ⟨⟨split.first, lt_of_le_of_lt firstLe slot.first.isLt⟩,
    ⟨split.second, lt_of_le_of_lt secondLe slot.second.isLt⟩,
    ⟨split.moment, lt_of_le_of_lt momentLe slot.moment.isLt⟩, ?_⟩
  exact (Nat.add_le_add (Nat.add_le_add firstLe secondLe) momentLe).trans slot.total_le

def upperRegularitySlot {grade : ℕ} {slot : RegularitySlot grade}
    (split : RegularitySlotSplit slot) : RegularitySlot grade := by
  let first := (slot.first : ℕ) - (split.first : ℕ)
  let second := (slot.second : ℕ) - (split.second : ℕ)
  let moment := (slot.moment : ℕ) - (split.moment : ℕ)
  have firstLe : first ≤ (slot.first : ℕ) := Nat.sub_le _ _
  have secondLe : second ≤ (slot.second : ℕ) := Nat.sub_le _ _
  have momentLe : moment ≤ (slot.moment : ℕ) := Nat.sub_le _ _
  exact ⟨⟨first, lt_of_le_of_lt firstLe slot.first.isLt⟩,
    ⟨second, lt_of_le_of_lt secondLe slot.second.isLt⟩,
    ⟨moment, lt_of_le_of_lt momentLe slot.moment.isLt⟩,
      (Nat.add_le_add (Nat.add_le_add firstLe secondLe) momentLe).trans slot.total_le⟩

def slotSplitMultiplicity {grade : ℕ} {slot : RegularitySlot grade}
    (split : RegularitySlotSplit slot) : ℕ :=
  Nat.choose (slot.first : ℕ) (split.first : ℕ) *
    Nat.choose (slot.second : ℕ) (split.second : ℕ) *
      Nat.choose (slot.moment : ℕ) (split.moment : ℕ)

@[simp] theorem slotDerivativeIndex_lower {grade : ℕ}
    {slot : RegularitySlot grade} (split : RegularitySlotSplit slot) :
    slotDerivativeIndex (lowerRegularitySlot split) =
      lowerDerivativeIndex (slotDerivativeIndex slot) (slotPhysicalSplit split) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;>
    simp [slotDerivativeIndex, lowerRegularitySlot, lowerDerivativeIndex,
      slotPhysicalSplit]

@[simp] theorem slotDerivativeIndex_upper {grade : ℕ}
    {slot : RegularitySlot grade} (split : RegularitySlotSplit slot) :
    slotDerivativeIndex (upperRegularitySlot split) =
      upperDerivativeIndex (slotDerivativeIndex slot) (slotPhysicalSplit split) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;>
    simp [slotDerivativeIndex, upperRegularitySlot, upperDerivativeIndex,
      slotPhysicalSplit]

theorem slotOrder_split {grade : ℕ} {slot : RegularitySlot grade}
    (split : RegularitySlotSplit slot) :
    slotOrder (lowerRegularitySlot split) + slotOrder (upperRegularitySlot split) =
      slotOrder slot := by
  have firstLe : (split.first : ℕ) ≤ (slot.first : ℕ) :=
    Nat.lt_succ_iff.mp split.first.isLt
  have secondLe : (split.second : ℕ) ≤ (slot.second : ℕ) :=
    Nat.lt_succ_iff.mp split.second.isLt
  have momentLe : (split.moment : ℕ) ≤ (slot.moment : ℕ) :=
    Nat.lt_succ_iff.mp split.moment.isLt
  simp only [slotOrder, lowerRegularitySlot, upperRegularitySlot]
  omega

theorem scaledCellWeight_additive (L ell : ℝ) (first second : ℤ) :
    scaledCellWeight L ell (first + second) ≤
      scaledCellWeight L ell first + scaledCellWeight L ell second := by
  let x : ℝ := (first : ℝ) * ell / L
  let y : ℝ := (second : ℝ) * ell / L
  have sumIdentity : ((first + second : ℤ) : ℝ) * ell / L = x + y := by
    dsimp [x, y]
    push_cast
    ring
  unfold scaledCellWeight
  rw [sumIdentity]
  change Real.sqrt (1 + (x + y) ^ 2) ≤
    Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + (x + y) ^ 2)]
  have absXLe : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]
    linarith
  have absYLe : |y| ≤ Real.sqrt (1 + y ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg y) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 1 + y ^ 2)]
    linarith
  have productXY : x * y ≤
      Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by
    calc
      x * y ≤ |x * y| := le_abs_self _
      _ = |x| * |y| := abs_mul x y
      _ ≤ Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) :=
        mul_le_mul absXLe absYLe (abs_nonneg y) (Real.sqrt_nonneg _)
  have rightSquare :
      (Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2)) ^ 2 =
        2 + x ^ 2 + y ^ 2 +
          2 * (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := by
    rw [add_sq, Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2),
      Real.sq_sqrt (by positivity : 0 ≤ 1 + y ^ 2)]
    ring
  rw [rightSquare]
  nlinarith

theorem scaledCellWeight_pow_le_binomial (L ell : ℝ) (first second : ℤ)
    (moment : ℕ) :
    scaledCellWeight L ell (first + second) ^ moment ≤
      ∑ split : Fin (moment + 1),
        (Nat.choose moment (split : ℕ) : ℝ) *
          scaledCellWeight L ell first ^ (split : ℕ) *
            scaledCellWeight L ell second ^ (moment - (split : ℕ)) := by
  calc
    scaledCellWeight L ell (first + second) ^ moment ≤
        (scaledCellWeight L ell first + scaledCellWeight L ell second) ^ moment :=
      pow_le_pow_left₀ (scaledCellWeight_nonnegative L ell (first + second))
        (scaledCellWeight_additive L ell first second) moment
    _ = _ := by
      rw [add_pow]
      rw [Fin.sum_univ_eq_sum_range (fun split : ℕ =>
        (Nat.choose moment split : ℝ) *
          scaledCellWeight L ell first ^ split *
            scaledCellWeight L ell second ^ (moment - split))]
      apply Finset.sum_congr rfl
      intro split splitMembership
      simp only [Finset.mem_range] at splitMembership
      ring

def coefficientMomentWeight (L sigma gamma ell : ℝ) (cell : ℤ)
    (moment : ℕ) (point : Grad.ClosedJets.ClosedDisk) : ℝ :=
  originalEnvelope sigma gamma ell cell point.val *
    scaledCellWeight L ell cell ^ moment

theorem coefficientMomentWeight_add_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (first second : ℤ)
    (moment : ℕ) (point : Grad.ClosedJets.ClosedDisk) :
    coefficientMomentWeight L sigma gamma ell (first + second) moment point ≤
      ∑ split : Fin (moment + 1),
        (Nat.choose moment (split : ℕ) : ℝ) *
          coefficientMomentWeight L sigma gamma ell first (split : ℕ) point *
            coefficientMomentWeight L sigma gamma ell second
              (moment - (split : ℕ)) point := by
  unfold coefficientMomentWeight
  have envelope := originalEnvelope_add_le admissible first second point
  have frequency := scaledCellWeight_pow_le_binomial L ell first second moment
  calc
    originalEnvelope sigma gamma ell (first + second) point.val *
        scaledCellWeight L ell (first + second) ^ moment ≤
      (originalEnvelope sigma gamma ell first point.val *
          originalEnvelope sigma gamma ell second point.val) *
        (∑ split : Fin (moment + 1),
          (Nat.choose moment (split : ℕ) : ℝ) *
            scaledCellWeight L ell first ^ (split : ℕ) *
              scaledCellWeight L ell second ^ (moment - (split : ℕ))) :=
      mul_le_mul envelope frequency
        (pow_nonneg (scaledCellWeight_nonnegative L ell _) _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro split _membership
      ring

end Grad.GaugeCoefficients.Neumann.Regularity
