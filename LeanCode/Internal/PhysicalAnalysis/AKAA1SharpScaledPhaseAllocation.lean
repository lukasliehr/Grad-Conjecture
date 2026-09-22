import GC18APRatio

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher

/-- Scaling the already proved full phase-ratio allocation introduces no
inverse cap radius. The constant depends on L and rank, not ell or cells. -/
theorem startupScaled_allocation_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (input shift : ℤ) :
    ell ^ rank * allocationPolynomial rank (input + shift) input ≤
      (rank + 1 : ℝ) * (max 1 L) ^ rank *
        scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ (rank - 1) := by
  have ellNonnegative := admissible_ell_nonnegative admissible
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have inputFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos input).le
  have shiftFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos shift).le
  have maximumNonnegative : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  have singleBound (split : ℕ) (membership : split ∈ Finset.Icc 1 rank) :
      ell ^ rank * (Grad.CellWeights.cellWeight shift ^ split *
        Grad.CellWeights.cellWeight input ^ (rank - split)) ≤
      (max 1 L) ^ rank * scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ (rank - 1) := by
    have splitBound := (Finset.mem_Icc.mp membership).2
    have splitIdentity : split + (rank - split) = rank := Nat.add_sub_of_le splitBound
    have ellPower : ell ^ rank = ell ^ split * ell ^ (rank - split) := by rw [← pow_add, splitIdentity]
    have maxPower : (max 1 L) ^ rank = (max 1 L) ^ split * (max 1 L) ^ (rank - split) := by
      rw [← pow_add, splitIdentity]
    calc
      _ = (ell * Grad.CellWeights.cellWeight shift) ^ split *
          (ell * Grad.CellWeights.cellWeight input) ^ (rank - split) := by
        simp only [mul_pow]
        rw [ellPower]
        ring
      _ ≤ (max 1 L * scaledCellWeight L ell shift) ^ split *
          (max 1 L * scaledCellWeight L ell input) ^ (rank - split) :=
        mul_le_mul
          (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell shift admissible.1
            ellNonnegative (admissible_ell_le_one admissible)) split)
          (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell input admissible.1
            ellNonnegative (admissible_ell_le_one admissible)) (rank - split))
          (by positivity) (by positivity)
      _ = (max 1 L) ^ rank *
          (scaledCellWeight L ell shift ^ split * scaledCellWeight L ell input ^ (rank - split)) := by
        simp only [mul_pow]
        rw [maxPower]
        ring
      _ ≤ (max 1 L) ^ rank *
          (scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ (rank - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg maximumNonnegative _)
        exact mul_le_mul (pow_le_pow_right₀ (scaledCellWeight_one_le L ell shift) splitBound)
          (pow_le_pow_right₀ (scaledCellWeight_one_le L ell input) (by have := (Finset.mem_Icc.mp membership).1; omega))
          (by positivity) (by positivity)
      _ = _ := by ring
  unfold allocationPolynomial
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _split ∈ Finset.Icc 1 rank,
        (max 1 L) ^ rank * scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ (rank - 1) :=
      Finset.sum_le_sum singleBound
    _ = (rank : ℝ) * ((max 1 L) ^ rank * scaledCellWeight L ell shift ^ rank *
        scaledCellWeight L ell input ^ (rank - 1)) := by simp
    _ ≤ (rank + 1 : ℝ) * ((max 1 L) ^ rank * scaledCellWeight L ell shift ^ rank *
        scaledCellWeight L ell input ^ (rank - 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end Grad.GaugeCoefficients.Physical.RadialLedger
