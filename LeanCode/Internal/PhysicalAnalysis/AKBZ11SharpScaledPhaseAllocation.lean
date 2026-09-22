import AKBZ10OriginalAdjustableMixedEndpoint
import AKAA3ActualAllocatedCoefficientBounds
import GC15Coherence

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.GaugeCoefficients.Physical.RadialLedger

/-- Keep the displacement order before summing the phase allocation. This
pays exactly d coefficient frequencies and a-d input frequencies. -/
theorem sharpScaled_phase_term {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank displacement : ℕ)
    (displacementLe : displacement ≤ rank) (input shift : ℤ) :
    ell^rank*(Grad.CellWeights.cellWeight shift^displacement*
      Grad.CellWeights.cellWeight input^(rank-displacement)) ≤
    (max 1 L)^rank*(scaledCellWeight L ell shift^displacement*
      scaledCellWeight L ell input^(rank-displacement)) := by
  have ellNonnegative := admissible_ell_nonnegative admissible
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have inputFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos input).le
  have shiftFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos shift).le
  have maximumNonnegative : 0≤max 1 L := zero_le_one.trans (le_max_left _ _)
  have power : displacement+(rank-displacement)=rank := Nat.add_sub_of_le displacementLe
  calc
    _ = (ell*Grad.CellWeights.cellWeight shift)^displacement*
      (ell*Grad.CellWeights.cellWeight input)^(rank-displacement) := by
        simp only [mul_pow]
        rw [show ell^rank=ell^displacement*ell^(rank-displacement) by rw [←pow_add,power]]
        ring
    _ ≤ (max 1 L*scaledCellWeight L ell shift)^displacement*
      (max 1 L*scaledCellWeight L ell input)^(rank-displacement) :=
      mul_le_mul
        (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell shift admissible.1
          (admissible_ell_nonnegative admissible) (admissible_ell_le_one admissible)) displacement)
        (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell input admissible.1
          (admissible_ell_nonnegative admissible) (admissible_ell_le_one admissible)) (rank-displacement))
        (by positivity) (by positivity)
    _ = _ := by
      simp only [mul_pow]
      rw [show (max 1 L)^rank=(max 1 L)^displacement*(max 1 L)^(rank-displacement) by rw [←pow_add,power]]
      ring

/-- The original phase allocation polynomial with the full sharp sum. -/
theorem sharpScaled_phase_allocation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (input shift : ℤ) :
    ell^rank*allocationPolynomial rank (input+shift) input ≤
    (max 1 L)^rank*∑ displacement ∈ Finset.Icc 1 rank,
      scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement) := by
  unfold allocationPolynomial
  simp only [add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_le_sum fun displacement membership =>
    sharpScaled_phase_term admissible rank displacement (Finset.mem_Icc.mp membership).2 input shift

end Grad.OriginalCartesianTameEstimate
